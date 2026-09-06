mod array;
mod declared;
mod generic;
mod index;
mod member;
mod object_type;
mod table_const;
mod tuple;

pub(in crate::semantic::type_check) use array::relate_array_to_array;
pub(in crate::semantic::type_check) use member::{
    collect_missing_members, relate_members, relate_target_intersection_index_members,
    unrelated_missing_members,
};
pub(in crate::semantic::type_check) use object_type::relate_object_to_object;

use crate::{
    LuaGenericType, LuaType, LuaTypeDecl, LuaTypeDeclId, TypeSubstitutor, VariadicType,
    semantic::type_check::error_chain::not_assignable_message,
};

use super::{
    callable::relate_callable,
    relation::{IntersectionState, Relater, RelationResult},
    sub_type::get_base_type_id,
};
use array::{
    relate_array_to_object, relate_array_to_tuple, relate_keyed_source_to_array,
    relate_table_generic_to_array,
};
use declared::relate_to_declared_target;
use generic::relate_same_family_generic_args;
use index::relate_to_table_generic;
use object_type::{relate_object_to_array, relate_object_to_tuple};
use table_const::{relate_table_const_to_array, relate_table_const_to_tuple};
use tuple::{
    relate_keyed_source_to_tuple, relate_tuple_to_array, relate_tuple_to_object,
    relate_tuple_to_tuple,
};

/// 结构化分发中心.
///
/// 返回 `None` 表示当前组合未处理, 由上层继续回退或判为不可赋值.
pub(in crate::semantic::type_check) fn dispatch_structured(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> Option<RelationResult> {
    match source {
        LuaType::Function | LuaType::DocFunction(_) | LuaType::Signature(_) => {
            return relate_callable(relater, source, target, intersection_state);
        }
        LuaType::Variadic(source_variadic) => {
            return Some(relate_variadic_source(
                relater,
                source,
                target,
                source_variadic,
                intersection_state,
            ));
        }
        LuaType::Ref(source_id) | LuaType::Def(source_id) => {
            if let Some(result) = relate_declared_source_capability(
                relater,
                source,
                source_id,
                target,
                intersection_state,
            ) {
                return Some(result);
            }
        }
        LuaType::Generic(source_generic) => {
            if let Some(result) = relate_generic_source_capability(
                relater,
                source,
                source_generic,
                target,
                intersection_state,
            ) {
                return Some(result);
            }
        }
        _ => {}
    }

    // 裸表可赋给任意结构目标
    if matches!(source, LuaType::Table)
        && matches!(
            target,
            LuaType::Table
                | LuaType::TableConst(_)
                | LuaType::Object(_)
                | LuaType::Tuple(_)
                | LuaType::Array(_)
                | LuaType::TableGeneric(_)
        )
    {
        return Some(Ok(()));
    }

    match target {
        LuaType::Ref(_) | LuaType::Def(_) | LuaType::Generic(_) => {
            relate_to_declared_target(relater, source, target, intersection_state)
        }
        LuaType::Object(target_object) => {
            let result = match source {
                LuaType::Object(source_object) => relate_object_to_object(
                    relater,
                    source,
                    target,
                    source_object,
                    target_object,
                    intersection_state,
                ),
                LuaType::Tuple(source_tuple) => relate_tuple_to_object(
                    relater,
                    source,
                    target,
                    source_tuple,
                    target_object,
                    intersection_state,
                ),
                LuaType::Array(source_array) => relate_array_to_object(
                    relater,
                    source,
                    target,
                    source_array,
                    target_object,
                    intersection_state,
                ),
                _ if is_structural_or_declared_source(source) => {
                    relate_members(relater, source, target, intersection_state)
                }
                _ => return None,
            };
            Some(result)
        }
        LuaType::TableConst(_) if is_structural_or_declared_source(source) => {
            Some(relate_members(relater, source, target, intersection_state))
        }
        LuaType::Tuple(target_tuple) => {
            let result = match source {
                LuaType::Tuple(source_tuple) => {
                    relate_tuple_to_tuple(relater, source_tuple, target_tuple, intersection_state)
                }
                LuaType::Array(source_array) => {
                    relate_array_to_tuple(relater, source_array, target_tuple, intersection_state)
                }
                LuaType::TableConst(source_range) => relate_table_const_to_tuple(
                    relater,
                    source_range,
                    target_tuple,
                    intersection_state,
                ),
                LuaType::Object(source_object) => {
                    relate_object_to_tuple(relater, source_object, target_tuple, intersection_state)
                }
                LuaType::Intersection(_) => {
                    relate_keyed_source_to_tuple(relater, source, target_tuple, intersection_state)
                }
                _ if is_declared_source(source) => {
                    relate_keyed_source_to_tuple(relater, source, target_tuple, intersection_state)
                }
                _ => return None,
            };
            Some(result)
        }
        LuaType::Array(target_array) => {
            let result = match source {
                LuaType::Array(source_array) => {
                    relate_array_to_array(relater, source_array, target_array, intersection_state)
                }
                LuaType::Tuple(source_tuple) => {
                    relate_tuple_to_array(relater, source_tuple, target_array, intersection_state)
                }
                LuaType::TableConst(source_range) => relate_table_const_to_array(
                    relater,
                    source,
                    target,
                    source_range,
                    target_array,
                    intersection_state,
                ),
                LuaType::Object(source_object) => relate_object_to_array(
                    relater,
                    source,
                    target,
                    source_object,
                    target_array,
                    intersection_state,
                ),
                LuaType::TableGeneric(source_params) => relate_table_generic_to_array(
                    relater,
                    source,
                    target,
                    source_params,
                    target_array,
                    intersection_state,
                ),
                _ if is_declared_source(source) => relate_keyed_source_to_array(
                    relater,
                    source,
                    target,
                    target_array,
                    intersection_state,
                ),
                _ => return None,
            };
            Some(result)
        }
        LuaType::TableGeneric(target_params)
            if is_structural_or_declared_source(source)
                && !matches!(source, LuaType::Intersection(_)) =>
        {
            Some(relate_to_table_generic(
                relater,
                source,
                target,
                target_params,
                intersection_state,
            ))
        }
        // 交集是否属于表由组成类型判定, 其余结构源可直接接受.
        LuaType::Table
            if is_structural_or_declared_source(source)
                && !matches!(source, LuaType::Intersection(_)) =>
        {
            Some(Ok(()))
        }
        LuaType::Userdata if is_declared_source(source) => Some(Ok(())),
        LuaType::Function | LuaType::DocFunction(_) | LuaType::Signature(_) => {
            relate_callable(relater, source, target, intersection_state)
        }
        // string/integer 在 std 内定义为类, 需要保留 class -> 基础类型豁免
        LuaType::String | LuaType::StringConst(_) | LuaType::Integer | LuaType::IntegerConst(_) => {
            let source_id = declared_source_id(source)?;
            let target_base_id = get_base_type_id(target)?;
            if *source_id == target_base_id {
                return Some(Ok(()));
            }
            Some(relater.fail(|db| not_assignable_message(db, source, target)))
        }
        _ => None,
    }
}

/// 可变参数源的关系.
fn relate_variadic_source(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    source_variadic: &VariadicType,
    intersection_state: IntersectionState,
) -> RelationResult {
    match source_variadic {
        VariadicType::Base(source_base) => match target {
            LuaType::Variadic(target_variadic) => match target_variadic.as_ref() {
                VariadicType::Base(target_base) => {
                    if source_base == target_base {
                        Ok(())
                    } else {
                        relater.fail(|db| not_assignable_message(db, source, target))
                    }
                }
                VariadicType::Multi(target_types) => {
                    for target_type in target_types {
                        relater.relate(source_base, target_type, intersection_state)?;
                    }
                    Ok(())
                }
            },
            _ => relater.relate(source_base, target, intersection_state),
        },
        VariadicType::Multi(_) => Ok(()),
    }
}

fn relate_declared_source_capability(
    relater: &mut Relater,
    source: &LuaType,
    source_id: &LuaTypeDeclId,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> Option<RelationResult> {
    let Some(source_decl) = relater.db().get_type_index().get_type_decl(source_id) else {
        return Some(relater.fail(|db| not_assignable_message(db, source, target)));
    };

    if source_decl.is_alias() {
        let Some(alias_origin) = source_decl.get_alias_ref() else {
            return Some(relater.fail(|db| not_assignable_message(db, source, target)));
        };
        return Some(relater.relate(alias_origin, target, intersection_state));
    }

    if source_decl.is_enum() {
        return Some(relate_enum_source(
            relater,
            source,
            source_id,
            source_decl,
            target,
            intersection_state,
        ));
    }

    None
}

/// enum 源表示运行时值域
fn relate_enum_source(
    relater: &mut Relater,
    source: &LuaType,
    source_id: &LuaTypeDeclId,
    source_decl: &LuaTypeDecl,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> RelationResult {
    if matches!(target, LuaType::Ref(target_id) | LuaType::Def(target_id) if target_id == source_id)
    {
        return Ok(());
    }

    // enum Def 表示运行时声明表, 只额外保留宽 Table 与 TableGeneric 关系.
    if matches!(source, LuaType::Def(_)) {
        match target {
            LuaType::Table => {
                return Ok(());
            }
            LuaType::TableGeneric(target_params) => {
                return relate_to_table_generic(
                    relater,
                    source,
                    target,
                    target_params,
                    intersection_state,
                );
            }
            _ => {}
        }
    }

    let Some(enum_fields) = source_decl.get_enum_field_type(relater.db()) else {
        return relater.fail(|db| not_assignable_message(db, source, target));
    };

    relater.relate(&enum_fields, target, intersection_state)
}

fn relate_generic_source_capability(
    relater: &mut Relater,
    source: &LuaType,
    source_generic: &LuaGenericType,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> Option<RelationResult> {
    let Some(source_decl) = relater
        .db()
        .get_type_index()
        .get_type_decl(source_generic.get_base_type_id_ref())
    else {
        return Some(relater.fail(|db| not_assignable_message(db, source, target)));
    };

    // 同族实参只探测一次. 非平凡关系仍需展开验证方差, 回退前恢复错误链.
    if let LuaType::Generic(target_generic) = target
        && source_generic.get_base_type_id_ref() == target_generic.get_base_type_id_ref()
        && !source_decl.is_enum()
    {
        if source_decl.is_class()
            && source_generic.get_params().len() != target_generic.get_params().len()
        {
            return Some(relater.fail(|db| not_assignable_message(db, source, target)));
        }
        let saved_chain = relater.error_chain_snapshot();
        if let Some(result) = relate_same_family_generic_args(
            relater,
            source_generic,
            target_generic,
            intersection_state,
        ) {
            return Some(result);
        }
        relater.restore_error_chain(saved_chain);
    }

    if source_decl.is_alias() {
        let substitutor = TypeSubstitutor::from_alias(
            source_generic.get_params().clone(),
            source_generic.get_base_type_id(),
        );
        return match source_decl.get_alias_origin(relater.db(), Some(&substitutor)) {
            Some(alias_origin) => Some(relater.relate(&alias_origin, target, intersection_state)),
            None => Some(relater.fail(|db| not_assignable_message(db, source, target))),
        };
    }

    if !source_decl.is_class() {
        return Some(relater.fail(|db| not_assignable_message(db, source, target)));
    }

    None
}

fn is_declared_source(source: &LuaType) -> bool {
    matches!(
        source,
        LuaType::Ref(_) | LuaType::Def(_) | LuaType::Generic(_)
    )
}

fn is_structural_or_declared_source(source: &LuaType) -> bool {
    matches!(
        source,
        LuaType::Table
            | LuaType::TableConst(_)
            | LuaType::Object(_)
            | LuaType::Tuple(_)
            | LuaType::Array(_)
            | LuaType::TableGeneric(_)
            | LuaType::Intersection(_)
    ) || is_declared_source(source)
}

fn declared_source_id(source: &LuaType) -> Option<&LuaTypeDeclId> {
    match source {
        LuaType::Ref(source_id) | LuaType::Def(source_id) => Some(source_id),
        LuaType::Generic(source_generic) => Some(source_generic.get_base_type_id_ref()),
        _ => None,
    }
}
