use std::sync::Arc;

use crate::{
    DbIndex, LuaArrayType, LuaObjectType, LuaType, LuaUnionType,
    semantic::type_check::{
        error_chain::{
            ChainMessage, ErrorChain, OverflowKind, not_assignable_message, push_message,
        },
        fast_eq_check, normalize_type,
    },
};

use super::{
    accept_reflexive_or_semantic,
    intersection::relate_intersection,
    simple::relate_simple,
    structured::{
        dispatch_structured, relate_array_to_array, relate_members, relate_object_to_object,
    },
    union::relate_union,
};

pub(crate) type RelationResult = Result<(), RelationFailure>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RelationFailure {
    Unrelated,
    Indeterminate(OverflowKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RelationOutcome {
    Related,
    Unrelated,
    Indeterminate(OverflowKind),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub(crate) struct IntersectionState(u32);

impl IntersectionState {
    pub(crate) const NONE: Self = Self(0);
    pub(crate) const SOURCE: Self = Self(1 << 0);
    pub(crate) const TARGET: Self = Self(1 << 1);

    pub(crate) fn contains(self, state: Self) -> bool {
        self.0 & state.0 != 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EvidenceMode {
    Silent,
    Explain,
}

fn relation_type_eq(source: &LuaType, target: &LuaType) -> bool {
    if let LuaType::FloatConst(left) = source {
        return matches!(target, LuaType::FloatConst(right) if left.to_bits() == right.to_bits());
    }
    if let LuaType::Object(left) = source {
        return matches!(target, LuaType::Object(right) if Arc::ptr_eq(left, right));
    }
    source == target
}

struct ActiveRelation<'active> {
    source: &'active LuaType,
    target: &'active LuaType,
    intersection_state: IntersectionState,
    parent: Option<&'active ActiveRelation<'active>>,
}

pub(crate) struct RelationSession<'db> {
    db: &'db DbIndex,
    evidence: EvidenceMode,
    relation_budget: u32,
    recursion_depth: u16,
    error_chain: Option<ErrorChain>,
}

pub(crate) struct Relater<'session, 'active, 'db> {
    session: &'session mut RelationSession<'db>,
    active_relation: Option<&'active ActiveRelation<'active>>,
}

impl<'db> RelationSession<'db> {
    fn new(db: &'db DbIndex, evidence: EvidenceMode) -> Self {
        Self {
            db,
            evidence,
            relation_budget: 20_000,
            recursion_depth: 0,
            error_chain: None,
        }
    }

    fn relate(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        let mut relater = Relater {
            session: self,
            active_relation: None,
        };
        relater.relate(source, target, intersection_state)
    }

    pub(crate) fn probe(db: &'db DbIndex, source: &LuaType, target: &LuaType) -> RelationOutcome {
        let mut session = Self::new(db, EvidenceMode::Silent);
        match session.relate(source, target, IntersectionState::NONE) {
            Ok(()) => RelationOutcome::Related,
            Err(RelationFailure::Unrelated) => RelationOutcome::Unrelated,
            Err(RelationFailure::Indeterminate(kind)) => RelationOutcome::Indeterminate(kind),
        }
    }

    pub(crate) fn explain(
        db: &'db DbIndex,
        source: &LuaType,
        target: &LuaType,
    ) -> super::AssignabilityResult {
        let mut session = Self::new(db, EvidenceMode::Explain);
        match session.relate(source, target, IntersectionState::NONE) {
            Ok(()) => super::AssignabilityResult::Assignable,
            Err(RelationFailure::Unrelated) => {
                super::AssignabilityResult::NotAssignable(session.error_chain)
            }
            Err(RelationFailure::Indeterminate(kind)) => {
                super::AssignabilityResult::Indeterminate(kind)
            }
        }
    }
}

impl<'session, 'active, 'db> Relater<'session, 'active, 'db> {
    pub(super) fn db(&self) -> &'db DbIndex {
        self.session.db
    }

    pub(super) fn is_explain(&self) -> bool {
        matches!(self.session.evidence, EvidenceMode::Explain)
    }

    pub(super) fn remaining_relation_budget(&self) -> usize {
        self.session.relation_budget as usize
    }

    pub(super) fn consume_relation_budget(&mut self) -> RelationResult {
        if self.session.relation_budget == 0 {
            return Err(RelationFailure::Indeterminate(OverflowKind::Budget));
        }
        self.session.relation_budget -= 1;
        Ok(())
    }

    pub(crate) fn relate(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        if accept_reflexive_or_semantic(source, target) {
            return Ok(());
        }

        // 高频结构组的直达通道
        if let Some(result) = self.try_structural_fast_dial(source, target, intersection_state) {
            return result;
        }

        // 游戏开发可能会为巨型配置表创建 ID 集合, 常量对枚举集合可直接快速命中
        if matches!(
            source,
            LuaType::IntegerConst(_) | LuaType::DocIntegerConst(_)
        ) && matches!(
            target,
            LuaType::Union(_) | LuaType::MultiLineUnion(_) | LuaType::Ref(_) | LuaType::Def(_)
        ) && accept_const_enum_member(self.session.db, source, target)
        {
            return Ok(());
        }

        // 简单类型关系
        if let Some(result) = relate_simple(self, source, target) {
            return result;
        }

        // 归一化和类型分解也会重入关系检查, 必须先建立递归防护.
        if self.session.recursion_depth >= 100 {
            return Err(RelationFailure::Indeterminate(OverflowKind::Recursion));
        }

        if is_scoped_type(source) || is_scoped_type(target) {
            if self.is_active_relation(source, target, intersection_state) {
                return Ok(());
            }
            self.consume_relation_budget()?;
            self.with_relation_scope(source, target, intersection_state, |relater| {
                relater.relate_in_scope(source, target, intersection_state)
            })
        } else {
            self.session.recursion_depth += 1;
            let result = self.relate_in_scope(source, target, intersection_state);
            self.session.recursion_depth -= 1;
            result
        }
    }

    fn relate_in_scope(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        // 归一化必须先于 union 分解, 否则别名展开会在每个 union 成员探测中重复执行.
        if let Some(normalized) = normalize_type(self.session.db, source)
            && normalized != *source
        {
            if matches!(source, LuaType::Ref(_)) && normalized == *target {
                return Ok(());
            }
            return self.relate(&normalized, target, intersection_state);
        }
        if let Some(normalized) = normalize_type(self.session.db, target)
            && normalized != *target
        {
            // 别名展开后可能与 source 结构相同
            if *source == normalized {
                return Ok(());
            }
            return self.relate(source, &normalized, intersection_state);
        }

        if matches!(target, LuaType::ModuleRef(_)) {
            return Ok(());
        }

        // 可分解类型: union/intersection 优先拆解
        if matches!(
            source,
            LuaType::Union(_) | LuaType::MultiLineUnion(_) | LuaType::Intersection(_)
        ) || matches!(
            target,
            LuaType::Union(_) | LuaType::MultiLineUnion(_) | LuaType::Intersection(_)
        ) {
            if let Some(result) = relate_union(self, source, target, intersection_state) {
                return result;
            }
            if let Some(result) = relate_intersection(self, source, target, intersection_state) {
                return result;
            }
        }

        // 同 id 的 constraint 是循环约束, 规范化无法解开, 判为不确定.
        if matches!(source, LuaType::TplRef(_)) || matches!(target, LuaType::TplRef(_)) {
            return Err(RelationFailure::Indeterminate(OverflowKind::Recursion));
        }

        // 终态
        if matches!(source, LuaType::Never) {
            return if matches!(target, LuaType::Never) {
                Ok(())
            } else {
                self.fail(|db| not_assignable_message(db, source, target))
            };
        }
        if matches!(target, LuaType::Never) {
            return self.fail(|db| not_assignable_message(db, source, target));
        }

        match dispatch_structured(self, source, target, intersection_state) {
            Some(result) => result,
            None => self.fail(|db| not_assignable_message(db, source, target)),
        }
    }

    /// 高频结构的直达通道
    fn try_structural_fast_dial(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> Option<RelationResult> {
        enum DialBody<'a> {
            Array(&'a LuaArrayType, &'a LuaArrayType),
            ObjectToObject(&'a LuaObjectType, &'a LuaObjectType),
            Members,
        }
        let body = match (source, target) {
            (LuaType::Array(source_array), LuaType::Array(target_array)) => {
                DialBody::Array(source_array, target_array)
            }
            (LuaType::Object(source_object), LuaType::Object(target_object)) => {
                DialBody::ObjectToObject(source_object, target_object)
            }
            (LuaType::TableConst(_), LuaType::Object(_)) => DialBody::Members,
            (
                LuaType::TableConst(_) | LuaType::Object(_),
                LuaType::Ref(target_id) | LuaType::Def(target_id),
            ) => {
                // 非别名非枚举的类目标直接比较成员.
                let target_decl = self.session.db.get_type_index().get_type_decl(target_id)?;
                if target_decl.is_alias() || target_decl.is_enum() {
                    return None;
                }
                DialBody::Members
            }
            _ => return None,
        };

        if self.session.recursion_depth >= 100 {
            return Some(Err(RelationFailure::Indeterminate(OverflowKind::Recursion)));
        }
        self.session.recursion_depth += 1;
        let result = match body {
            DialBody::Array(source_array, target_array) => {
                relate_array_to_array(self, source_array, target_array, intersection_state)
            }
            DialBody::ObjectToObject(source_object, target_object) => relate_object_to_object(
                self,
                source,
                target,
                source_object,
                target_object,
                intersection_state,
            ),
            DialBody::Members => relate_members(self, source, target, intersection_state),
        };
        self.session.recursion_depth -= 1;
        Some(result)
    }

    fn is_active_relation(
        &self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> bool {
        let mut active = self.active_relation;
        while let Some(relation) = active {
            if relation.intersection_state == intersection_state
                && relation_type_eq(relation.source, source)
                && relation_type_eq(relation.target, target)
            {
                return true;
            }
            active = relation.parent;
        }
        false
    }

    /// 创建完整的活动关系作用域, 用于处理复杂类型.
    fn with_relation_scope(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
        body: impl FnOnce(&mut Relater<'_, '_, 'db>) -> RelationResult,
    ) -> RelationResult {
        self.session.recursion_depth += 1;
        let active_relation = ActiveRelation {
            source,
            target,
            intersection_state,
            parent: self.active_relation,
        };
        let mut relater = Relater {
            session: &mut *self.session,
            active_relation: Some(&active_relation),
        };
        let result = body(&mut relater);
        self.session.recursion_depth -= 1;
        result
    }

    /// 关系探测, 用于选出候选结果
    pub(super) fn probe_relation(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationOutcome {
        let evidence = self.session.evidence;
        self.session.evidence = EvidenceMode::Silent;
        let result = self.relate(source, target, intersection_state);
        self.session.evidence = evidence;
        match result {
            Ok(()) => RelationOutcome::Related,
            Err(RelationFailure::Unrelated) => RelationOutcome::Unrelated,
            Err(RelationFailure::Indeterminate(kind)) => RelationOutcome::Indeterminate(kind),
        }
    }

    /// 在叶子失败时调用, 用于构建具体的错误
    pub(crate) fn fail(
        &mut self,
        message: impl FnOnce(&DbIndex) -> ChainMessage,
    ) -> RelationResult {
        if self.is_explain() {
            let message = message(self.session.db);
            self.push_error_message(message);
        }
        Err(RelationFailure::Unrelated)
    }

    /// 在中间层调用, 如果发生错误时将构建错误链
    pub(crate) fn on_unrelated(
        &mut self,
        result: RelationResult,
        message: impl FnOnce(&DbIndex) -> ChainMessage,
    ) -> RelationResult {
        if let Err(RelationFailure::Unrelated) = &result
            && self.is_explain()
        {
            let message = message(self.session.db);
            self.push_error_message(message);
        }
        result
    }

    fn push_error_message(&mut self, message: ChainMessage) {
        let head = self.session.error_chain.take();
        self.session.error_chain = Some(push_message(head, message));
    }

    pub(super) fn error_chain_snapshot(&self) -> Option<ErrorChain> {
        self.session.error_chain.clone()
    }

    pub(super) fn restore_error_chain(&mut self, snapshot: Option<ErrorChain>) {
        self.session.error_chain = snapshot;
    }
}

/// 常量对巨型枚举集合的快速命中.
fn accept_const_enum_member(db: &DbIndex, source: &LuaType, target: &LuaType) -> bool {
    let target_origin = match target {
        LuaType::Union(_) => Some(target),
        LuaType::Ref(target_id) => db
            .get_type_index()
            .get_type_decl(target_id)
            .and_then(|target_decl| target_decl.get_alias_ref()),
        _ => None,
    };
    match target_origin {
        Some(LuaType::MultiLineUnion(union)) => union
            .get_unions()
            .iter()
            .any(|(candidate, _)| fast_eq_check(source, candidate)),
        Some(LuaType::Union(union)) => match union.as_ref() {
            LuaUnionType::Basic(_) => false,
            LuaUnionType::Nullable(candidate) => fast_eq_check(source, candidate),
            LuaUnionType::Multi(candidates) => candidates
                .iter()
                .any(|candidate| fast_eq_check(source, candidate)),
        },
        _ => false,
    }
}

/// 环检测仅在涉及声明/实例/签名/约束等可能成环的类型时启用.
fn is_scoped_type(typ: &LuaType) -> bool {
    match typ {
        LuaType::Ref(_)
        | LuaType::Def(_)
        | LuaType::Generic(_)
        | LuaType::Signature(_)
        | LuaType::Instance(_)
        | LuaType::Call(_)
        | LuaType::Conditional(_)
        | LuaType::Mapped(_)
        | LuaType::MultiLineUnion(_)
        | LuaType::TypeGuard(_)
        | LuaType::ModuleRef(_) => true,
        LuaType::TplRef(tpl) => tpl.get_constraint().is_some(),
        _ => false,
    }
}
