use crate::{
    LuaMemberKey, LuaType,
    semantic::type_check::error_chain::{
        ChainMessage, index_message, not_assignable_message, property_message,
    },
};

use super::super::relation::{IntersectionState, Relater, RelationFailure, RelationResult};
use super::{member::MemberView, tuple::visit_tuple_index_entries};

#[derive(Clone, Copy)]
enum EntryOrigin<'a> {
    Generic,
    Tuple(usize),
    Field(&'a LuaMemberKey),
    Index,
}

/// 按需读取键值项, 保留错误定位所需的来源信息.
fn visit_index_entries(
    relater: &mut Relater,
    source: &LuaType,
    mut visitor: impl FnMut(&mut Relater, &LuaType, &LuaType, EntryOrigin<'_>) -> RelationResult,
) -> RelationResult {
    match source {
        LuaType::Array(array) => visitor(
            relater,
            &LuaType::Integer,
            array.get_base(),
            EntryOrigin::Generic,
        ),
        LuaType::Tuple(tuple) => visit_tuple_index_entries(tuple, |key, value, index| {
            visitor(relater, key, value, EntryOrigin::Tuple(index))
        }),
        LuaType::TableGeneric(params) if params.len() == 2 => {
            visitor(relater, &params[0], &params[1], EntryOrigin::Generic)
        }
        LuaType::Object(object) => {
            for (key, value) in object.get_fields() {
                if let Some(key_type) = key.to_index_type() {
                    visitor(relater, &key_type, value, EntryOrigin::Field(key))?;
                }
            }
            for (key, value) in object.get_index_access() {
                visitor(relater, key, value, EntryOrigin::Index)?;
            }
            Ok(())
        }
        _ => MemberView::new(relater, source).visit_types(relater, |relater, key, value| {
            if let Some(key_type) = key.to_index_type() {
                visitor(relater, &key_type, value, EntryOrigin::Field(key))?;
            }
            Ok(())
        }),
    }
}

pub(super) fn relate_index_member(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    target_key_type: &LuaType,
    target_value_type: &LuaType,
    intersection_state: IntersectionState,
) -> RelationResult {
    // 源交集的组成类型分支不单独承担目标索引义务.
    if intersection_state.contains(IntersectionState::SOURCE) {
        return Ok(());
    }
    if let LuaType::Intersection(intersection) = source {
        for member in intersection.get_types() {
            relate_index_member(
                relater,
                member,
                target,
                target_key_type,
                target_value_type,
                intersection_state,
            )?;
        }
        return Ok(());
    }

    visit_index_entries(relater, source, |relater, key, value, origin| {
        relater.consume_relation_budget()?;
        match relater.probe_relation(key, target_key_type, intersection_state) {
            Ok(()) => {
                let result = relater.relate(value, target_value_type, intersection_state);
                relater.on_unrelated(result, |db| index_message(db, key))
            }
            Err(RelationFailure::Unrelated) => {
                if matches!(origin, EntryOrigin::Tuple(_)) && matches!(key, LuaType::Integer) {
                    relater.fail(|db| not_assignable_message(db, source, target))
                } else {
                    Ok(())
                }
            }
            Err(RelationFailure::Indeterminate(kind)) => Err(RelationFailure::Indeterminate(kind)),
        }
    })
}

/// table<K, V> 要求每个键值项都满足 K 和 V.
pub(super) fn relate_to_table_generic(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    target_params: &[LuaType],
    intersection_state: IntersectionState,
) -> RelationResult {
    if target_params.len() != 2
        || matches!(source, LuaType::TableGeneric(params) if params.len() != 2)
    {
        return relater.fail(|db| not_assignable_message(db, source, target));
    }

    visit_index_entries(relater, source, |relater, key, value, origin| {
        if !matches!(origin, EntryOrigin::Generic) {
            relater.consume_relation_budget()?;
        }
        let key_result = relater.relate(key, &target_params[0], intersection_state);
        relater.on_unrelated(key_result, |db| match origin {
            EntryOrigin::Generic | EntryOrigin::Tuple(_) => {
                ChainMessage::GenericArgument { index: 0 }
            }
            _ => index_message(db, key),
        })?;
        let value_result = relater.relate(value, &target_params[1], intersection_state);
        relater.on_unrelated(value_result, |db| match origin {
            EntryOrigin::Generic => ChainMessage::GenericArgument { index: 1 },
            EntryOrigin::Tuple(index) => ChainMessage::TupleElement { index },
            EntryOrigin::Field(key) => property_message(key),
            EntryOrigin::Index => index_message(db, key),
        })
    })
}
