use crate::{
    LuaArrayType, LuaMemberKey, LuaObjectType, LuaType,
    semantic::type_check::error_chain::{index_message, not_assignable_message, property_message},
};

use super::super::relation::{IntersectionState, Relater, RelationResult};
use super::array::effective_array_base;

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
