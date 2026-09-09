use hashbrown::Equivalent;
use std::{rc::Rc, sync::Arc};

use crate::{
    DbIndex, LuaType, LuaUnionType,
    semantic::cache::{SemanticLocalCache, TypeCacheEntry},
};

use super::{
    error_chain::{ChainMessage, ErrorChain, OverflowKind, not_assignable_message, push_message},
    fast_eq_check,
    intersection::relate_intersection,
    normalize_type,
    simple::is_simple_assignable,
    structured::dispatch_structured,
    union::relate_union,
};

pub(crate) type RelationResult = Result<(), RelationFailure>;
type RelationKey = (LuaType, LuaType, IntersectionState);

#[derive(Hash)]
struct BorrowedRelationKey<'a>(&'a LuaType, &'a LuaType, IntersectionState);

impl Equivalent<RelationKey> for BorrowedRelationKey<'_> {
    fn equivalent(&self, key: &RelationKey) -> bool {
        self.0 == &key.0 && self.1 == &key.1 && self.2 == key.2
    }
}

impl BorrowedRelationKey<'_> {
    fn into_owned(self) -> RelationKey {
        (self.0.clone(), self.1.clone(), self.2)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RelationFailure {
    Unrelated,
    Indeterminate(OverflowKind),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssignabilityResult {
    Assignable,
    NotAssignable(Option<ErrorChain>),
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
pub(crate) enum EvidenceMode {
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

pub(crate) struct Relater<'db> {
    db: &'db DbIndex,
    cache: &'db mut SemanticLocalCache,
    evidence: EvidenceMode,
    relation_budget: u32,
    recursion_depth: u16,
    pub(crate) error_chain: Option<ErrorChain>,
    assumption_count: usize,
    active_relations: Vec<RelationKey>,
}

impl<'db> Relater<'db> {
    pub(crate) fn new(
        db: &'db DbIndex,
        cache: &'db mut SemanticLocalCache,
        evidence: EvidenceMode,
    ) -> Self {
        Self {
            db,
            cache,
            evidence,
            relation_budget: 20_000,
            recursion_depth: 0,
            error_chain: None,
            assumption_count: 0,
            active_relations: Vec::new(),
        }
    }

    pub(super) fn db(&self) -> &'db DbIndex {
        self.db
    }

    pub(super) fn type_entry(&mut self, typ: &LuaType) -> Rc<TypeCacheEntry> {
        self.cache.type_entry(typ)
    }

    pub(super) fn is_explain(&self) -> bool {
        matches!(self.evidence, EvidenceMode::Explain)
    }

    pub(super) fn consume_relation_budget(&mut self) -> RelationResult {
        if self.relation_budget == 0 {
            return Err(RelationFailure::Indeterminate(OverflowKind::Budget));
        }
        self.relation_budget -= 1;
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn relate(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        if let Some(related) = is_simple_assignable(source, target) {
            return if related {
                Ok(())
            } else {
                self.fail(|db| not_assignable_message(db, source, target))
            };
        }
        self.relate_complex(source, target, intersection_state)
    }

    pub(crate) fn relate_complex(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        if matches!(
            source,
            LuaType::IntegerConst(_)
                | LuaType::DocIntegerConst(_)
                | LuaType::StringConst(_)
                | LuaType::DocStringConst(_)
        ) && accept_const_enum_member(self.db, source, target)
        {
            return Ok(());
        }

        let key = BorrowedRelationKey(source, target, intersection_state);
        if let Some(&related) = self.cache.relations.get(&key) {
            if related {
                return Ok(());
            }
            // 失败缓存只供探测复用, 诊断仍需重建当前错误链.
            if !self.is_explain() {
                return Err(RelationFailure::Unrelated);
            }
        }

        let assumption_count = self.assumption_count;
        let is_root = self.recursion_depth == 0;
        let result = self.relate_uncached(source, target, intersection_state);
        match result {
            Ok(()) if is_root || assumption_count == self.assumption_count => {
                self.cache.relations.insert(key.into_owned(), true);
            }
            Err(RelationFailure::Unrelated) => {
                self.cache.relations.insert(key.into_owned(), false);
            }
            _ => {}
        }
        result
    }

    fn relate_uncached(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        if self.recursion_depth >= 100 {
            return Err(RelationFailure::Indeterminate(OverflowKind::Recursion));
        }

        let scoped = is_scoped_type(source) || is_scoped_type(target);
        if scoped {
            if self.is_active_relation(source, target, intersection_state) {
                // 依赖闭环假设的子关系成功不能提前写入共享缓存.
                self.assumption_count += 1;
                return Ok(());
            }
            self.consume_relation_budget()?;
            self.active_relations
                .push((source.clone(), target.clone(), intersection_state));
        }
        self.recursion_depth += 1;
        let result = self.relate_in_scope(source, target, intersection_state);
        self.recursion_depth -= 1;
        if scoped {
            self.active_relations.pop();
        }
        result
    }

    fn relate_in_scope(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        // 归一化必须先于 union 分解, 否则别名展开会在每个 union 成员探测中重复执行.
        if let Some(normalized) = normalize_type(self.db, source)
            && normalized != *source
        {
            if matches!(source, LuaType::Ref(_)) && normalized == *target {
                return Ok(());
            }
            return self.relate(&normalized, target, intersection_state);
        }
        if let Some(normalized) = normalize_type(self.db, target)
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

    fn is_active_relation(
        &self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> bool {
        self.active_relations
            .iter()
            .rev()
            .any(|(active_source, active_target, state)| {
                *state == intersection_state
                    && relation_type_eq(active_source, source)
                    && relation_type_eq(active_target, target)
            })
    }

    /// 关系探测, 用于选出候选结果
    pub(super) fn probe_relation(
        &mut self,
        source: &LuaType,
        target: &LuaType,
        intersection_state: IntersectionState,
    ) -> RelationResult {
        let evidence = self.evidence;
        self.evidence = EvidenceMode::Silent;
        let result = self.relate(source, target, intersection_state);
        self.evidence = evidence;
        result
    }

    /// 在叶子失败时调用, 用于构建具体的错误
    pub(crate) fn fail(
        &mut self,
        message: impl FnOnce(&DbIndex) -> ChainMessage,
    ) -> RelationResult {
        if self.is_explain() {
            let message = message(self.db);
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
            let message = message(self.db);
            self.push_error_message(message);
        }
        result
    }

    fn push_error_message(&mut self, message: ChainMessage) {
        let head = self.error_chain.take();
        self.error_chain = Some(push_message(head, message));
    }

    pub(super) fn error_chain_snapshot(&self) -> Option<ErrorChain> {
        self.error_chain.clone()
    }

    pub(super) fn restore_error_chain(&mut self, snapshot: Option<ErrorChain>) {
        self.error_chain = snapshot;
    }
}

/// 常量对枚举/联合体集合的快速早退命中.
#[inline(always)]
fn accept_const_enum_member(db: &DbIndex, source: &LuaType, target: &LuaType) -> bool {
    let target = match target {
        LuaType::Union(_) | LuaType::MultiLineUnion(_) => Some(target),
        LuaType::Ref(id) => db
            .get_type_index()
            .get_type_decl(id)
            .and_then(|decl| decl.get_alias_ref()),
        _ => None,
    };
    match target {
        Some(LuaType::MultiLineUnion(union)) => union
            .get_unions()
            .iter()
            .any(|(candidate, _)| fast_eq_check(source, candidate)),
        Some(LuaType::Union(union)) => match union.as_ref() {
            LuaUnionType::Basic(_) => false,
            LuaUnionType::Nullable(candidate) => fast_eq_check(source, candidate),
            LuaUnionType::Multi(candidates) => candidates
                .get_types()
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

#[cfg(test)]
mod tests {
    use crate::{VirtualWorkspace, semantic::cache::SemanticLocalCache};

    use super::{
        AssignabilityResult, ChainMessage, EvidenceMode, IntersectionState, OverflowKind, Relater,
        RelationFailure,
    };
    use crate::semantic::type_check::{check_assignable, probe_assignable};

    // 根类型关系检查失败时, 不会缓存因子类型递归闭环假设而得出的推测性成功.
    #[test]
    fn failed_root_does_not_cache_success_from_recursive_assumptions() {
        let mut ws = VirtualWorkspace::new();
        ws.def(
            r#"
            ---@class CacheRootSource
            ---@field child CacheChildSource
            ---@field value string
            ---@class CacheRootTarget
            ---@field child CacheChildTarget
            ---@field value number
            ---@class CacheChildSource
            ---@field back CacheRootSource
            ---@class CacheChildTarget
            ---@field back CacheRootTarget
        "#,
        );
        let source = ws.ty("CacheRootSource");
        let target = ws.ty("CacheRootTarget");
        let child_source = ws.ty("CacheChildSource");
        let child_target = ws.ty("CacheChildTarget");
        let db = ws.analysis.compilation.get_db();
        let mut cache = SemanticLocalCache::default();
        let mut relater = Relater::new(db, &mut cache, EvidenceMode::Silent);
        assert_eq!(
            relater.relate(&source, &target, IntersectionState::NONE),
            Err(RelationFailure::Unrelated)
        );
        assert!(relater.assumption_count > 0);
        assert_eq!(relater.recursion_depth, 0);
        assert!(relater.active_relations.is_empty());
        let child_key = (
            child_source.clone(),
            child_target.clone(),
            IntersectionState::NONE,
        );
        assert!(!cache.relations.contains_key(&child_key));
        assert_eq!(
            probe_assignable(db, &child_source, &child_target, Some(&mut cache)),
            Err(RelationFailure::Unrelated)
        );
        assert_eq!(cache.relations.get(&child_key), Some(&false));
    }

    // 根级递归类型检查成功后会被正确缓存, 后续复用无需消耗关系预算.
    #[test]
    fn successful_recursive_root_can_be_reused_without_budget() {
        let mut ws = VirtualWorkspace::new();
        ws.def(
            r#"
            ---@class CacheRecursiveSource
            ---@field next CacheRecursiveSource
            ---@class CacheRecursiveTarget
            ---@field next CacheRecursiveTarget
        "#,
        );
        let source = ws.ty("CacheRecursiveSource");
        let target = ws.ty("CacheRecursiveTarget");
        let db = ws.analysis.compilation.get_db();
        let mut cache = SemanticLocalCache::default();
        let mut relater = Relater::new(db, &mut cache, EvidenceMode::Silent);
        assert_eq!(
            relater.relate(&source, &target, IntersectionState::NONE),
            Ok(())
        );
        assert!(relater.assumption_count > 0);
        assert_eq!(relater.recursion_depth, 0);
        assert!(relater.active_relations.is_empty());
        relater.relation_budget = 0;
        assert_eq!(
            relater.relate(&source, &target, IntersectionState::NONE),
            Ok(())
        );
    }

    // 预算超限或递归过深导致的不确定结果不会留下缓存, 且能正确清理活跃作用域.
    #[test]
    fn indeterminate_relations_leave_no_cache_or_active_scope() {
        let mut ws = VirtualWorkspace::new();
        ws.def(
            r#"
            ---@class CacheLimitedSource
            ---@field next CacheLimitedSource
            ---@class CacheLimitedTarget
            ---@field next CacheLimitedTarget
        "#,
        );
        let source = ws.ty("CacheLimitedSource");
        let target = ws.ty("CacheLimitedTarget");
        let db = ws.analysis.compilation.get_db();
        for kind in [OverflowKind::Budget, OverflowKind::Recursion] {
            let mut cache = SemanticLocalCache::default();
            let mut relater = Relater::new(db, &mut cache, EvidenceMode::Silent);
            let initial_depth = match kind {
                OverflowKind::Budget => {
                    relater.relation_budget = 1;
                    0
                }
                OverflowKind::Recursion => 99,
            };
            relater.recursion_depth = initial_depth;
            assert_eq!(
                relater.relate(&source, &target, IntersectionState::NONE),
                Err(RelationFailure::Indeterminate(kind))
            );
            assert_eq!(relater.recursion_depth, initial_depth);
            assert!(relater.active_relations.is_empty());
            assert!(relater.cache.relations.is_empty());
            relater.recursion_depth = 0;
            relater.relation_budget = 20_000;
            assert_eq!(
                relater.relate(&source, &target, IntersectionState::NONE),
                Ok(())
            );
        }
    }

    // 探测失败结果已缓存时, 诊断模式仍能正确重建字段不匹配与缺失成员的错误链.
    #[test]
    fn failed_probe_rebuilds_the_same_field_and_missing_member_diagnostics() {
        let mut ws = VirtualWorkspace::new();
        let cases = [
            (
                ws.ty("{ branch: { value: string } }"),
                ws.ty("{ branch: { value: number } }"),
            ),
            (
                ws.ty("{ id: string }"),
                ws.ty("{ id: string, name: string, count: number }"),
            ),
        ];
        let db = ws.analysis.compilation.get_db();
        for (index, (source, target)) in cases.into_iter().enumerate() {
            let expected = check_assignable(db, &source, &target, None);
            let AssignabilityResult::NotAssignable(Some(chain)) = &expected else {
                panic!("expected a diagnostic for incompatible members");
            };
            if index == 0 {
                assert_eq!(
                    chain.message(),
                    &ChainMessage::Field {
                        name: "branch.value".into()
                    }
                );
            } else {
                assert!(matches!(chain.message(), ChainMessage::MissingMembers(_)));
            }
            let mut cache = SemanticLocalCache::default();
            assert_eq!(
                probe_assignable(db, &source, &target, Some(&mut cache)),
                Err(RelationFailure::Unrelated)
            );
            for _ in 0..2 {
                assert_eq!(
                    check_assignable(db, &source, &target, Some(&mut cache)),
                    expected
                );
            }
        }
    }
}
