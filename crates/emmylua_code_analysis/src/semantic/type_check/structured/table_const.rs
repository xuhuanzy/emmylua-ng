use crate::{
    LuaArrayType, LuaMemberKey, LuaType,
    semantic::type_check::error_chain::{not_assignable_message, property_message},
};

use super::super::relation::{IntersectionState, Relater, RelationResult};
use super::{array::effective_array_base, member::MemberView};

pub(super) fn relate_table_const_to_array(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    target_array: &LuaArrayType,
    intersection_state: IntersectionState,
) -> RelationResult {
    let target_base = effective_array_base(relater, target_array.get_base());
    let db = relater.db();
    let source_members = MemberView::new(relater, source);
    if source_members.is_empty(db) {
        return Ok(());
    }

    let mut checked = false;
    source_members.visit(db, |key, member| {
        relater.consume_relation_budget()?;
        if !matches!(key, LuaMemberKey::Integer(index) if *index > 0) {
            return Ok(());
        }
        let source_type = member.typ(db);
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
