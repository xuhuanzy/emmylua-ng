use std::borrow::Cow;

use crate::{
    DbIndex, LuaIntersectionType, LuaMemberIndexItem, LuaMemberKey, LuaMemberOwner, LuaType,
    semantic::type_check::error_chain::{missing_members_message, property_message},
};

use super::super::{
    is_optional,
    relation::{IntersectionState, Relater, RelationFailure, RelationResult},
};
use super::index::relate_index_member;

pub(super) fn visit_member_items<E>(
    db: &DbIndex,
    owner: &LuaMemberOwner,
    mut visitor: impl FnMut(&LuaMemberKey, &LuaMemberIndexItem) -> Result<(), E>,
) -> Result<(), E> {
    let Some(mut member_items) = db.get_member_index().get_member_items(owner) else {
        return Ok(());
    };
    member_items.try_for_each(|(key, item)| visitor(key, item))
}

/// 访问对象, 常量表和声明类型的成员, 简单对象直接借用已有字段.
#[inline]
pub(super) fn visit_members(
    relater: &mut Relater,
    typ: &LuaType,
    mut visitor: impl FnMut(&mut Relater, &LuaMemberKey, &LuaType) -> RelationResult,
) -> RelationResult {
    match typ {
        LuaType::Object(object) => {
            for (key, member_type) in object.get_fields() {
                visitor(relater, key, member_type)?;
            }
            for (key_type, member_type) in object.get_index_access() {
                visitor(
                    relater,
                    &LuaMemberKey::TypeKey(key_type.clone()),
                    member_type,
                )?;
            }
            Ok(())
        }
        LuaType::TableConst(range) => {
            let db = relater.db();
            visit_member_items(db, &LuaMemberOwner::Element(range.clone()), |key, item| {
                visitor(relater, key, &item.resolve_type(db).unwrap_or(LuaType::Any))
            })
        }
        LuaType::Ref(_) | LuaType::Def(_) | LuaType::Generic(_) => {
            let entry = relater.type_entry(typ);
            let db = relater.db();
            for (key, member) in entry.members(db, typ) {
                visitor(relater, key, member.typ(db))?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

#[inline]
pub(in crate::semantic::type_check) fn relate_members(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> RelationResult {
    if relater.is_explain() {
        let (missing_keys, _) =
            collect_missing_members(relater, source, target, intersection_state)?;
        if !missing_keys.is_empty() {
            return unrelated_missing_members(relater, source, target, missing_keys);
        }
    }

    visit_members(relater, target, |relater, key, member_type| {
        if let LuaMemberKey::TypeKey(key_type) = key {
            if intersection_state.contains(IntersectionState::TARGET) {
                return Ok(());
            }
            return relate_index_member(
                relater,
                source,
                target,
                key_type,
                member_type,
                intersection_state,
            );
        }
        relate_keyed_member(relater, source, key, member_type, intersection_state)
    })
}

#[inline(always)]
fn relate_keyed_member(
    relater: &mut Relater,
    source: &LuaType,
    key: &LuaMemberKey,
    target_member_type: &LuaType,
    intersection_state: IntersectionState,
) -> RelationResult {
    relater.consume_relation_budget()?;
    let source_member_type = find_source_member_type(relater, source, key, intersection_state)?;
    let Some(source_member_type) = source_member_type else {
        // Explain 模式在此时必然经过了缺失字段判断, 因此可以直接跳过
        if relater.is_explain() || is_optional(relater.db(), target_member_type) {
            return Ok(());
        }
        return relater.fail(|db| {
            missing_members_message(db, source, target_member_type, std::slice::from_ref(key))
        });
    };

    let field_result = relater.relate(&source_member_type, target_member_type, intersection_state);
    relater.on_unrelated(field_result, |_| property_message(key))
}

#[inline(always)]
pub(super) fn find_source_member_type<'source>(
    relater: &mut Relater,
    source: &'source LuaType,
    key: &LuaMemberKey,
    intersection_state: IntersectionState,
) -> Result<Option<Cow<'source, LuaType>>, RelationFailure> {
    let member_type = match source {
        LuaType::Object(object) => object
            .get_field(key)
            .or_else(|| {
                let LuaMemberKey::TypeKey(key_type) = key else {
                    return None;
                };
                object
                    .get_index_access()
                    .iter()
                    .find_map(|(index_type, value_type)| {
                        (index_type == key_type).then_some(value_type)
                    })
            })
            .map(Cow::Borrowed),
        LuaType::TableConst(range) => relater
            .db()
            .get_member_index()
            .get_member_item(&LuaMemberOwner::Element(range.clone()), key)
            .map(|item| Cow::Owned(item.resolve_type(relater.db()).unwrap_or(LuaType::Any))),
        LuaType::Ref(_)
        | LuaType::Def(_)
        | LuaType::Generic(_)
        | LuaType::Union(_)
        | LuaType::MultiLineUnion(_)
        | LuaType::Intersection(_) => {
            let entry = relater.type_entry(source);
            entry.member_type(relater.db(), source, key).map(Cow::Owned)
        }
        LuaType::Tuple(source_tuple) => match key {
            LuaMemberKey::Integer(index) if *index > 0 => source_tuple
                .get_type(*index as usize - 1)
                .map(Cow::Borrowed),
            _ => None,
        },
        LuaType::Array(source_array) => match key {
            LuaMemberKey::Integer(index) if *index > 0 => {
                Some(Cow::Borrowed(source_array.get_base()))
            }
            LuaMemberKey::TypeKey(key_type) if key_type.is_integer() => {
                Some(Cow::Borrowed(source_array.get_base()))
            }
            _ => None,
        },
        LuaType::TableGeneric(source_params) if source_params.len() == 2 => {
            let Some(source_key_type) = key.to_index_type() else {
                return Ok(None);
            };
            match relater.probe_relation(&source_key_type, &source_params[0], intersection_state) {
                Ok(()) => Some(Cow::Borrowed(&source_params[1])),
                Err(RelationFailure::Unrelated) => None,
                Err(RelationFailure::Indeterminate(kind)) => {
                    return Err(RelationFailure::Indeterminate(kind));
                }
            }
        }
        _ => None,
    };
    Ok(member_type)
}

pub(in crate::semantic::type_check) fn relate_target_intersection_index_members(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    intersection: &LuaIntersectionType,
) -> RelationResult {
    for member in intersection.get_types() {
        if let LuaType::Intersection(nested) = member {
            relate_target_intersection_index_members(relater, source, target, nested)?;
            continue;
        }
        visit_members(relater, member, |relater, key, value_type| {
            let LuaMemberKey::TypeKey(key_type) = key else {
                return Ok(());
            };
            relate_index_member(
                relater,
                source,
                target,
                key_type,
                value_type,
                IntersectionState::NONE,
            )
        })?;
    }
    Ok(())
}

/// 收集 target 中 source 缺失且不可空的 keyed 成员
pub(in crate::semantic::type_check) fn collect_missing_members(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> Result<(Vec<LuaMemberKey>, bool), RelationFailure> {
    let mut missing_keys = Vec::new();
    let mut has_shared_key = false;
    if let LuaType::TableConst(range) = target {
        let db = relater.db();
        // 只有缺失字段才需要解析目标类型来判断是否可空.
        visit_member_items(db, &LuaMemberOwner::Element(range.clone()), |key, item| {
            if matches!(key, LuaMemberKey::TypeKey(_)) {
                return Ok(());
            }
            if find_source_member_type(relater, source, key, intersection_state)?.is_some() {
                has_shared_key = true;
            } else if !is_optional(db, &item.resolve_type(db).unwrap_or(LuaType::Any)) {
                missing_keys.push(key.clone());
            }
            Ok(())
        })?;
    } else {
        visit_members(relater, target, |relater, key, member_type| {
            if matches!(key, LuaMemberKey::TypeKey(_)) {
                return Ok(());
            }
            if find_source_member_type(relater, source, key, intersection_state)?.is_some() {
                has_shared_key = true;
            } else if !is_optional(relater.db(), member_type) {
                missing_keys.push(key.clone());
            }
            Ok(())
        })?;
    }
    Ok((missing_keys, has_shared_key))
}

/// 探测目标成员在 source 中是否缺失且不可空.
pub(super) fn probe_missing_member(
    relater: &mut Relater,
    source: &LuaType,
    key: &LuaMemberKey,
    target_member_type: &LuaType,
    intersection_state: IntersectionState,
) -> Result<bool, RelationFailure> {
    if find_source_member_type(relater, source, key, intersection_state)?.is_some() {
        return Ok(false);
    }
    Ok(!is_optional(relater.db(), target_member_type))
}

/// 用收集到的全部缺失字段构建整体失败.
pub(in crate::semantic::type_check) fn unrelated_missing_members(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    keys: Vec<LuaMemberKey>,
) -> RelationResult {
    relater.fail(|db| missing_members_message(db, source, target, &keys))
}

#[cfg(test)]
mod tests {
    use crate::{
        VirtualWorkspace,
        semantic::{
            cache::SemanticLocalCache,
            type_check::{RelationFailure, probe_assignable},
        },
    };

    #[test]
    fn declared_sequences_use_all_duplicate_index_declarations() {
        let mut ws = VirtualWorkspace::new();
        ws.def(
            r#"
            ---@class CacheArrayValues<T>
            ---@field [integer] T
            ---@field [integer] number
            ---@class CacheTupleValues<T>
            ---@field [1] T
            ---@field [1] number
            ---@class CacheInheritedArray: CacheArrayValues<string>
            ---@class CacheInheritedTuple: CacheTupleValues<string>
        "#,
        );
        for (source, narrow, wide) in [
            (
                "CacheArrayValues<string>",
                "string[]",
                "(string | number)[]",
            ),
            ("CacheInheritedArray", "string[]", "(string | number)[]"),
            ("CacheTupleValues<string>", "[string]", "[string | number]"),
            ("CacheInheritedTuple", "[string]", "[string | number]"),
        ] {
            let source = ws.ty(source);
            let narrow = ws.ty(narrow);
            let wide = ws.ty(wide);
            let db = ws.analysis.compilation.get_db();
            let mut cache = SemanticLocalCache::default();
            assert_eq!(
                probe_assignable(db, &source, &narrow, Some(&mut cache)),
                Err(RelationFailure::Unrelated)
            );
            assert_eq!(
                probe_assignable(db, &source, &wide, Some(&mut cache)),
                Ok(())
            );
        }
    }
}
