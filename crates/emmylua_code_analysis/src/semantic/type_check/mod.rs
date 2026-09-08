use std::sync::Arc;

mod callable;
mod error_chain;
mod intersection;
mod relation;
mod simple;
mod structured;
mod sub_type;
mod test;
mod union;

use relation::{EvidenceMode, Relater};
use simple::is_simple_assignable;

pub use error_chain::{
    ChainMessage, ErrorChain, MissingMembersMessage, OverflowKind, chain_node, push_message,
};
pub use relation::AssignabilityResult;
pub(crate) use relation::{IntersectionState, RelationFailure, RelationResult};
pub use sub_type::is_sub_type_of;

use crate::{
    BasicTypeKind, DbIndex, GenericTpl, LuaAliasCallKind, LuaType, LuaUnionType, TypeSubstitutor,
    instantiate_type_generic, semantic::cache::SemanticLocalCache,
};

/// 无法确定的关系按可赋值处理, 只有确定不兼容时才拒绝.
pub(crate) fn is_assignable(
    db: &DbIndex,
    source: &LuaType,
    target: &LuaType,
    cache: Option<&mut SemanticLocalCache>,
) -> bool {
    !matches!(
        probe_assignable(db, source, target, cache),
        Err(RelationFailure::Unrelated)
    )
}

pub(crate) fn probe_assignable(
    db: &DbIndex,
    source: &LuaType,
    target: &LuaType,
    cache: Option<&mut SemanticLocalCache>,
) -> RelationResult {
    if let Some(related) = is_simple_assignable(source, target) {
        return if related {
            Ok(())
        } else {
            Err(RelationFailure::Unrelated)
        };
    }
    let mut local_cache = None;
    let cache = cache.unwrap_or_else(|| local_cache.insert(SemanticLocalCache::default()));
    Relater::new(db, cache, EvidenceMode::Silent).relate_complex(
        source,
        target,
        IntersectionState::NONE,
    )
}

pub(crate) fn check_assignable(
    db: &DbIndex,
    source: &LuaType,
    target: &LuaType,
    cache: Option<&mut SemanticLocalCache>,
) -> AssignabilityResult {
    let mut local_cache = None;
    let cache = cache.unwrap_or_else(|| local_cache.insert(SemanticLocalCache::default()));
    let mut relater = Relater::new(db, cache, EvidenceMode::Explain);
    match relater.relate(source, target, IntersectionState::NONE) {
        Ok(()) => AssignabilityResult::Assignable,
        Err(RelationFailure::Unrelated) => AssignabilityResult::NotAssignable(relater.error_chain),
        Err(RelationFailure::Indeterminate(kind)) => AssignabilityResult::Indeterminate(kind),
    }
}

#[inline(always)]
pub fn fast_eq_check(source: &LuaType, target: &LuaType) -> bool {
    match (source, target) {
        (LuaType::Ref(a) | LuaType::Def(a), LuaType::Ref(b) | LuaType::Def(b)) => a == b,
        (LuaType::Any, _) => true,
        (_, LuaType::Any | LuaType::Unknown) => true,
        (LuaType::SelfInfer, _) | (_, LuaType::SelfInfer) => true,
        (LuaType::Nil, LuaType::Nil)
        | (LuaType::Table, LuaType::Table)
        | (LuaType::Userdata, LuaType::Userdata)
        | (LuaType::Function, LuaType::Function)
        | (LuaType::Thread, LuaType::Thread)
        | (LuaType::Boolean, LuaType::Boolean)
        | (LuaType::String, LuaType::String)
        | (LuaType::Integer, LuaType::Integer)
        | (LuaType::Number, LuaType::Number)
        | (LuaType::Io, LuaType::Io)
        | (LuaType::Global, LuaType::Global)
        | (LuaType::Never, LuaType::Never) => true,
        (
            LuaType::BooleanConst(a) | LuaType::DocBooleanConst(a),
            LuaType::BooleanConst(b) | LuaType::DocBooleanConst(b),
        ) => a == b,
        (
            LuaType::StringConst(a) | LuaType::DocStringConst(a),
            LuaType::StringConst(b) | LuaType::DocStringConst(b),
        ) => a == b,
        (
            LuaType::IntegerConst(a) | LuaType::DocIntegerConst(a),
            LuaType::IntegerConst(b) | LuaType::DocIntegerConst(b),
        ) => a == b,
        (LuaType::FloatConst(a), LuaType::FloatConst(b)) => a == b,
        (LuaType::TableConst(a), LuaType::TableConst(b)) => a == b,
        (LuaType::Ref(a), LuaType::Union(b)) => matches!(
            b.as_ref(),
            LuaUnionType::Nullable(LuaType::Ref(b)) if a == b
        ),
        (LuaType::Array(a), LuaType::Array(b)) => Arc::ptr_eq(a, b),
        (LuaType::Tuple(a), LuaType::Tuple(b)) => Arc::ptr_eq(a, b),
        (LuaType::DocFunction(a), LuaType::DocFunction(b)) => Arc::ptr_eq(a, b),
        (LuaType::Object(a), LuaType::Object(b)) => Arc::ptr_eq(a, b),
        (LuaType::Union(a), LuaType::Union(b)) => Arc::ptr_eq(a, b),
        (LuaType::Intersection(a), LuaType::Intersection(b)) => Arc::ptr_eq(a, b),
        (LuaType::Generic(a), LuaType::Generic(b)) => Arc::ptr_eq(a, b) || a == b,
        (LuaType::TableGeneric(a), LuaType::TableGeneric(b)) => Arc::ptr_eq(a, b),
        (LuaType::TplRef(a), LuaType::TplRef(b)) => Arc::ptr_eq(a, b),
        (LuaType::StrTplRef(a), LuaType::StrTplRef(b)) => Arc::ptr_eq(a, b),
        (LuaType::Variadic(a), LuaType::Variadic(b)) => Arc::ptr_eq(a, b),
        (LuaType::Signature(a), LuaType::Signature(b)) => a == b,
        (LuaType::Instance(a), LuaType::Instance(b)) => Arc::ptr_eq(a, b),
        (LuaType::Namespace(a), LuaType::Namespace(b)) => a == b,
        (LuaType::Call(a), LuaType::Call(b)) => Arc::ptr_eq(a, b),
        (LuaType::MultiLineUnion(a), LuaType::MultiLineUnion(b)) => Arc::ptr_eq(a, b),
        (LuaType::TypeGuard(a), LuaType::TypeGuard(b)) => Arc::ptr_eq(a, b),
        (LuaType::Language(a), LuaType::Language(b)) => a == b,
        (LuaType::ModuleRef(a), LuaType::ModuleRef(b)) => a == b,
        (LuaType::TplRef(a), _) | (_, LuaType::TplRef(a)) if a.get_constraint().is_none() => true,
        _ => false,
    }
}

#[inline(always)]
pub fn normalize_type(db: &DbIndex, typ: &LuaType) -> Option<LuaType> {
    // 禁止在此对泛型进行展开
    match typ {
        LuaType::TplRef(tpl) if !is_circular_tpl_constraint(tpl) => tpl
            .get_constraint()
            .filter(|constraint| *constraint != typ)
            .cloned(),
        LuaType::Ref(type_id) => {
            let type_decl = db.get_type_index().get_type_decl(type_id)?;
            if type_decl.is_alias() {
                return type_decl.get_alias_ref().cloned();
            }
            None
        }
        LuaType::Call(alias_call)
            if matches!(
                alias_call.get_call_kind(),
                LuaAliasCallKind::Index | LuaAliasCallKind::RawGet | LuaAliasCallKind::KeyOf
            ) && !typ.contain_tpl() =>
        {
            let resolved = instantiate_type_generic(db, typ, &TypeSubstitutor::new());
            (resolved != *typ).then_some(resolved)
        }
        LuaType::Instance(instance) => Some(instance.get_base().clone()),
        LuaType::MultiLineUnion(union) => Some(union.to_union()),
        LuaType::TypeGuard(_) => Some(LuaType::Boolean),
        LuaType::ModuleRef(file_id) => db
            .get_module_index()
            .get_module(*file_id)
            .and_then(|module| module.export_type.clone()),
        _ => None,
    }
}

pub(super) fn is_circular_tpl_constraint(tpl: &GenericTpl) -> bool {
    matches!(
        tpl.get_constraint(),
        Some(LuaType::TplRef(constraint_tpl))
            if constraint_tpl.get_tpl_id() == tpl.get_tpl_id()
    )
}

/// 快速判断是否可空, 结果为`false`时并不是准确的
pub fn is_optional(db: &DbIndex, typ: &LuaType) -> bool {
    is_optional_inner(db, typ, 0)
}

fn is_optional_inner(db: &DbIndex, typ: &LuaType, depth: usize) -> bool {
    const MAX_DEPTH: usize = 8;
    if depth > MAX_DEPTH {
        return false;
    }

    match typ {
        LuaType::Nil | LuaType::Any | LuaType::Unknown | LuaType::Variadic(_) => true,
        LuaType::Union(union) => match union.as_ref() {
            LuaUnionType::Basic(basic) => basic.contains(BasicTypeKind::Nil),
            LuaUnionType::Nullable(_) => true,
            LuaUnionType::Multi(types) => types.iter().any(|t| is_optional_inner(db, t, depth + 1)),
        },
        LuaType::MultiLineUnion(union) => union
            .get_unions()
            .iter()
            .any(|(t, _)| is_optional_inner(db, t, depth + 1)),
        LuaType::Ref(type_id) | LuaType::Def(type_id) => {
            if let Some(type_decl) = db.get_type_index().get_type_decl(type_id) {
                if let Some(alias_origin) = type_decl.get_alias_ref() {
                    return is_optional_inner(db, alias_origin, depth + 1);
                }
            }
            false
        }
        LuaType::Generic(generic) => {
            let base_id = generic.get_base_type_id_ref();
            if let Some(type_decl) = db.get_type_index().get_type_decl(base_id) {
                if let Some(alias_origin) = type_decl.get_alias_ref() {
                    return is_optional_inner(db, alias_origin, depth + 1);
                }
            }
            false
        }
        LuaType::Instance(instance) => is_optional_inner(db, instance.get_base(), depth + 1),
        LuaType::TplRef(tpl) => {
            if let Some(constraint) = tpl.get_constraint() {
                if constraint != typ {
                    return is_optional_inner(db, constraint, depth + 1);
                }
            }
            false
        }
        _ => false,
    }
}
