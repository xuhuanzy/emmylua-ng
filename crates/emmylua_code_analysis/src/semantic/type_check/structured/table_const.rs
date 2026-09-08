use crate::{
    InFiled, LuaArrayType, LuaMemberKey, LuaMemberOwner, LuaType,
    semantic::type_check::error_chain::{not_assignable_message, property_message},
};

use super::super::{
    OverflowKind,
    relation::{IntersectionState, Relater, RelationFailure, RelationResult},
};

use super::{array::effective_array_base, member::visit_member_items};

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
