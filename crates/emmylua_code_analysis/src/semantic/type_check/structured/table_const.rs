use crate::{
    InFiled, LuaArrayType, LuaMemberKey, LuaMemberOwner, LuaTupleType, LuaType,
    semantic::type_check::error_chain::{ChainMessage, not_assignable_message, property_message},
};

use super::super::{
    OverflowKind, is_optional,
    relation::{IntersectionState, Relater, RelationFailure, RelationResult},
};

use super::{array::effective_array_base, member::visit_member_items};

pub(super) fn relate_table_const_to_tuple(
    relater: &mut Relater,
    range: &InFiled<rowan::TextRange>,
    target_tuple: &LuaTupleType,
    intersection_state: IntersectionState,
) -> RelationResult {
    let owner = LuaMemberOwner::Element(range.clone());
    for (index, target_type) in target_tuple.get_types().iter().enumerate() {
        relater.consume_relation_budget()?;
        let key = LuaMemberKey::Integer(index as i64 + 1);
        let source_type = relater
            .db()
            .get_member_index()
            .get_member_item(&owner, &key)
            .map(|item| item.resolve_type(relater.db()).unwrap_or(LuaType::Any));
        let Some(source_type) = source_type else {
            if is_optional(relater.db(), target_type) {
                continue;
            }
            return relater.fail(|_| ChainMessage::MissingTupleElement { index });
        };
        let result = relater.relate(&source_type, target_type, intersection_state);
        relater.on_unrelated(result, |_| ChainMessage::TupleElement { index })?;
    }
    Ok(())
}

pub(super) fn relate_table_const_to_array(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    range: &InFiled<rowan::TextRange>,
    target_array: &LuaArrayType,
    intersection_state: IntersectionState,
) -> RelationResult {
    let target_base = effective_array_base(relater, target_array.get_base());
    let owner = LuaMemberOwner::Element(range.clone());
    let member_len = relater.db().get_member_index().get_member_len(&owner);
    if member_len == 0 {
        return Ok(());
    }
    if member_len > relater.remaining_relation_budget() {
        return Err(RelationFailure::Indeterminate(OverflowKind::Budget));
    }

    let db = relater.db();
    let mut checked = false;
    visit_member_items(db, &owner, |key, item| {
        if !matches!(key, LuaMemberKey::Integer(index) if *index > 0) {
            return Ok(());
        }
        relater.consume_relation_budget()?;
        let source_type = item.resolve_type(db).unwrap_or(LuaType::Any);
        let result = relater.relate(&source_type, &target_base, intersection_state);
        relater.on_unrelated(result, |_| property_message(key))?;
        checked = true;
        Ok(())
    })?;

    if checked {
        Ok(())
    } else {
        relater.fail(|db| not_assignable_message(db, source, target))
    }
}
