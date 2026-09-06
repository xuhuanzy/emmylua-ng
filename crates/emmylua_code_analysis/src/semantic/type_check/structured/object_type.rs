use crate::{
    LuaArrayType, LuaMemberKey, LuaObjectType, LuaTupleType, LuaType,
    semantic::type_check::error_chain::{
        ChainMessage, index_message, missing_members_message, not_assignable_message,
        property_message,
    },
};

use super::super::{
    is_optional,
    relation::{IntersectionState, Relater, RelationResult},
};
use super::{
    array::effective_array_base, index::relate_index_member, member::unrelated_missing_members,
};

pub(super) fn relate_object_to_tuple(
    relater: &mut Relater,
    source_object: &LuaObjectType,
    target_tuple: &LuaTupleType,
    intersection_state: IntersectionState,
) -> RelationResult {
    for (index, target_type) in target_tuple.get_types().iter().enumerate() {
        relater.consume_relation_budget()?;
        let key = LuaMemberKey::Integer(index as i64 + 1);
        let Some(source_type) = source_object.get_field(&key) else {
            if is_optional(relater.db(), target_type) {
                continue;
            }
            return relater.fail(|_| ChainMessage::MissingTupleElement { index });
        };
        let result = relater.relate(source_type, target_type, intersection_state);
        relater.on_unrelated(result, |_| ChainMessage::TupleElement { index })?;
    }
    Ok(())
}

pub(super) fn relate_object_to_array(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    source_object: &LuaObjectType,
    target_array: &LuaArrayType,
    intersection_state: IntersectionState,
) -> RelationResult {
    let target_base = effective_array_base(relater, target_array.get_base());
    let mut checked = false;
    for (key, source_type) in source_object.get_fields() {
        if !matches!(key, LuaMemberKey::Integer(index) if *index > 0) {
            continue;
        }
        relater.consume_relation_budget()?;
        let result = relater.relate(source_type, &target_base, intersection_state);
        relater.on_unrelated(result, |_| property_message(&key))?;
        checked = true;
    }
    for (source_key, source_type) in source_object.get_index_access() {
        if !source_key.is_integer() {
            continue;
        }
        relater.consume_relation_budget()?;
        let result = relater.relate(source_type, &target_base, intersection_state);
        relater.on_unrelated(result, |db| index_message(db, source_key))?;
        checked = true;
    }

    if checked {
        Ok(())
    } else {
        relater.fail(|db| not_assignable_message(db, source, target))
    }
}

#[inline(always)]
pub(in crate::semantic::type_check) fn relate_object_to_object(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    source_object: &LuaObjectType,
    target_object: &LuaObjectType,
    intersection_state: IntersectionState,
) -> RelationResult {
    // 对于解释模式, 我们应先做可空判断.
    if relater.is_explain() {
        let mut missing_keys = Vec::new();
        for (target_key, target_member_type) in target_object.get_fields() {
            if source_object.get_field(target_key).is_none()
                && !is_optional(relater.db(), target_member_type)
            {
                missing_keys.push(target_key.clone());
            }
        }
        if !missing_keys.is_empty() {
            return unrelated_missing_members(relater, source, target, missing_keys);
        }
    }

    for (target_key, target_member_type) in target_object.get_fields() {
        relater.consume_relation_budget()?;
        let source_member_type = source_object.get_field(target_key);
        let Some(source_member_type) = source_member_type else {
            if relater.is_explain() || is_optional(relater.db(), target_member_type) {
                continue;
            }
            return relater.fail(|db| {
                missing_members_message(db, source, target, std::slice::from_ref(target_key))
            });
        };

        let field_result =
            relater.relate(source_member_type, target_member_type, intersection_state);
        let result = relater.on_unrelated(field_result, |_| property_message(target_key));
        result?;
    }

    if !intersection_state.contains(IntersectionState::TARGET) {
        for (target_key_type, target_value_type) in target_object.get_index_access() {
            relate_index_member(
                relater,
                source,
                target,
                target_key_type,
                target_value_type,
                intersection_state,
            )?;
        }
    }

    Ok(())
}
