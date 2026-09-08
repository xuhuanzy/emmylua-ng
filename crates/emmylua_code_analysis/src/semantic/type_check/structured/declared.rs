use crate::{
    LuaGenericType, LuaType, LuaTypeDeclId, TypeSubstitutor, complete_type_generic_args_in_type,
    semantic::type_check::error_chain::not_assignable_message,
};

use super::super::{
    relation::{IntersectionState, Relater, RelationResult},
    sub_type::{get_base_type_id, is_sub_type_of},
};
use super::{
    array::relate_array_to_declared_target, member::relate_members,
    tuple::relate_tuple_to_declared_target,
};

pub(super) fn relate_to_declared_target(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> Option<RelationResult> {
    let target_id = match target {
        LuaType::Ref(target_id) | LuaType::Def(target_id) => target_id,
        LuaType::Generic(target_generic) => target_generic.get_base_type_id_ref(),
        _ => return None,
    };
    let Some(target_decl) = relater.db().get_type_index().get_type_decl(target_id) else {
        return Some(relater.fail(|db| not_assignable_message(db, source, target)));
    };

    if target_decl.is_alias() {
        let target_substitutor = match target {
            LuaType::Generic(target_generic) => Some(TypeSubstitutor::from_alias(
                target_generic.get_params().clone(),
                target_generic.get_base_type_id(),
            )),
            _ => None,
        };
        let Some(origin_type) =
            target_decl.get_alias_origin(relater.db(), target_substitutor.as_ref())
        else {
            return Some(relater.fail(|db| not_assignable_message(db, source, target)));
        };
        let origin_contains_source = match &*origin_type {
            LuaType::Union(origin_union) => origin_union.into_vec().contains(source),
            _ => *origin_type == *source,
        };
        if origin_contains_source {
            return Some(Ok(()));
        }
        return Some(relater.relate(source, &origin_type, intersection_state));
    }

    if target_decl.is_enum() {
        let Some(enum_fields) = target_decl.get_enum_field_type(relater.db()) else {
            return Some(relater.fail(|db| not_assignable_message(db, source, target)));
        };

        // enum 参与位运算时结果会被推断为 Integer, 但直接写入整数常量仍需匹配 enum 字段.
        if let LuaType::Union(enum_types) = &enum_fields
            && enum_types
                .into_vec()
                .iter()
                .all(|typ| matches!(typ, LuaType::DocIntegerConst(_) | LuaType::IntegerConst(_)))
            && matches!(source, LuaType::Integer)
        {
            return Some(Ok(()));
        }

        return Some(relater.relate(source, &enum_fields, intersection_state));
    }

    // 过滤非类形态的源
    if !matches!(
        source,
        LuaType::Ref(_)
            | LuaType::Def(_)
            | LuaType::Generic(_)
            | LuaType::Userdata
            | LuaType::Thread
            | LuaType::Global
            | LuaType::Table
            | LuaType::Array(_)
            | LuaType::Tuple(_)
            | LuaType::TableConst(_)
            | LuaType::Object(_)
            | LuaType::TableGeneric(_)
            | LuaType::Intersection(_)
    ) {
        return None;
    }

    Some(relate_to_class_target(
        relater,
        source,
        target,
        target_id,
        intersection_state,
    ))
}

fn relate_to_class_target(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    target_id: &LuaTypeDeclId,
    intersection_state: IntersectionState,
) -> RelationResult {
    match source {
        LuaType::Table | LuaType::Global => Ok(()),
        LuaType::Ref(source_id) | LuaType::Def(source_id) => {
            if let LuaType::Generic(target_generic) = target {
                relate_class_to_generic_target(
                    relater,
                    source,
                    source_id,
                    target,
                    target_generic,
                    intersection_state,
                )
            } else if is_same_decl(target, source_id) {
                Ok(())
            } else {
                relate_members(relater, source, target, intersection_state)
            }
        }
        LuaType::Generic(source_generic) => {
            if is_same_decl(target, source_generic.get_base_type_id_ref()) {
                Ok(())
            } else {
                relate_members(relater, source, target, intersection_state)
            }
        }
        // 内置类型沿继承链判定.
        LuaType::Thread | LuaType::Userdata => {
            if let Some(base_id) = get_base_type_id(source)
                && is_sub_type_of(relater.db(), target_id, &base_id)
            {
                Ok(())
            } else {
                relater.fail(|db| not_assignable_message(db, source, target))
            }
        }
        LuaType::Array(source_array) => relate_array_to_declared_target(
            relater,
            source,
            target,
            source_array,
            intersection_state,
        ),
        LuaType::Tuple(source_tuple) => relate_tuple_to_declared_target(
            relater,
            source,
            target,
            source_tuple,
            intersection_state,
        ),
        LuaType::TableConst(_)
        | LuaType::Object(_)
        | LuaType::TableGeneric(_)
        | LuaType::Intersection(_) => relate_members(relater, source, target, intersection_state),
        _ => Ok(()),
    }
}

fn is_same_decl(target: &LuaType, source_id: &LuaTypeDeclId) -> bool {
    matches!(target, LuaType::Ref(target_id) | LuaType::Def(target_id) if target_id == source_id)
}

fn relate_class_to_generic_target(
    relater: &mut Relater,
    source: &LuaType,
    source_id: &LuaTypeDeclId,
    target: &LuaType,
    target_generic: &LuaGenericType,
    intersection_state: IntersectionState,
) -> RelationResult {
    let completed_source = complete_type_generic_args_in_type(relater.db(), source);
    if completed_source != *source && matches!(completed_source, LuaType::Generic(_)) {
        return relater.relate(&completed_source, target, intersection_state);
    }

    if source_id == target_generic.get_base_type_id_ref() {
        if target_generic.get_params().iter().all(|param| {
            param.is_any() || matches!(param, LuaType::TplRef(_) | LuaType::StrTplRef(_))
        }) {
            return Ok(());
        }
        return relater.fail(|db| not_assignable_message(db, source, target));
    }

    relate_members(relater, source, target, intersection_state)
}
