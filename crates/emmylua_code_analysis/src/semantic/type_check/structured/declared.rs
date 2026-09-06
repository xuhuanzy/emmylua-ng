use hashbrown::HashSet;

use crate::{
    DbIndex, LuaGenericType, LuaMemberIndexItem, LuaMemberKey, LuaMemberOwner, LuaType,
    LuaTypeDeclId, TypeSubstitutor, complete_type_generic_args_in_type, instantiate_type_generic,
    semantic::type_check::error_chain::not_assignable_message,
};

use super::super::{
    relation::{IntersectionState, Relater, RelationResult},
    sub_type::{get_base_type_id, is_sub_type_of},
};
use super::{
    array::relate_array_to_declared_target,
    member::{relate_members, visit_member_items},
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

pub(super) fn visit_declared_members(
    relater: &mut Relater,
    declared_type: &LuaType,
    mut visitor: impl FnMut(&mut Relater, &LuaMemberKey, &LuaType) -> RelationResult,
) -> RelationResult {
    let mut seen_keys = HashSet::new();
    let mut visited_types = HashSet::new();
    visit_declared_type_members(
        relater,
        declared_type,
        &mut seen_keys,
        &mut visited_types,
        &mut visitor,
    )
}

fn visit_declared_type_members(
    relater: &mut Relater,
    declared_type: &LuaType,
    seen_keys: &mut HashSet<LuaMemberKey>,
    visited_types: &mut HashSet<LuaTypeDeclId>,
    visitor: &mut impl FnMut(&mut Relater, &LuaMemberKey, &LuaType) -> RelationResult,
) -> RelationResult {
    // 用于为实例化后的对象类型提供快速路径
    match declared_type {
        LuaType::Object(object) => {
            for (key, member_type) in object.get_fields() {
                if !seen_keys.insert(key.clone()) {
                    continue;
                }
                visitor(relater, key, member_type)?;
            }
            for (key_type, member_type) in object.get_index_access() {
                let key = LuaMemberKey::TypeKey(key_type.clone());
                if !seen_keys.insert(key.clone()) {
                    continue;
                }
                visitor(relater, &key, member_type)?;
            }
            return Ok(());
        }
        LuaType::TableGeneric(params) if params.len() == 2 => {
            let key = LuaMemberKey::TypeKey(params[0].clone());
            if seen_keys.insert(key.clone()) {
                visitor(relater, &key, &params[1])?;
            }
            return Ok(());
        }
        LuaType::Tuple(tuple) => {
            for (index, member_type) in tuple.get_types().iter().enumerate() {
                let key = LuaMemberKey::Integer(index as i64 + 1);
                if !seen_keys.insert(key.clone()) {
                    continue;
                }
                visitor(relater, &key, member_type)?;
            }
            return Ok(());
        }
        LuaType::Array(array) => {
            let key = LuaMemberKey::TypeKey(LuaType::Integer);
            if seen_keys.insert(key.clone()) {
                visitor(relater, &key, array.get_base())?;
            }
            return Ok(());
        }
        _ => {}
    }

    let (type_id, substitutor, generic_params) = match declared_type {
        LuaType::Ref(type_id) | LuaType::Def(type_id) => (type_id.clone(), None, None),
        LuaType::Generic(generic) => (
            generic.get_base_type_id(),
            Some(TypeSubstitutor::from_type_array(
                generic.get_params().clone(),
            )),
            Some(generic.get_params()),
        ),
        _ => return Ok(()),
    };
    let db = relater.db();
    let owner = LuaMemberOwner::Type(type_id.clone());
    let type_decl = db.get_type_index().get_type_decl(&type_id);
    let is_alias = type_decl.as_ref().is_some_and(|decl| decl.is_alias());
    let has_supers = db
        .get_type_index()
        .get_super_types_iter(&type_id)
        .is_some_and(|mut supers| supers.next().is_some());

    // alias 的有效成员位于 origin, 需要落到慢路径的 alias 回退, 不进快路径.
    if !has_supers && !is_alias && seen_keys.is_empty() {
        // 非泛型成员直接复用索引键, 避免宽对象关系检查为每个字段复制键.
        let Some(substitutor) = substitutor.as_ref() else {
            visit_member_items(db, &owner, |key, item| {
                let Ok(member_type) = item.resolve_type(db) else {
                    return Ok(());
                };
                visitor(relater, key, &member_type)
            })?;
            return Ok(());
        };
        visit_member_items(db, &owner, |key, item| {
            let Some((key, member_type)) = resolve_instantiated_member(db, key, item, substitutor)
            else {
                return Ok(());
            };
            visitor(relater, &key, &member_type)
        })?;
        return Ok(());
    }

    if !visited_types.insert(type_id.clone()) {
        return Ok(());
    }

    if let Some(substitutor) = substitutor.as_ref() {
        visit_member_items(db, &owner, |key, item| {
            let Some((key, member_type)) = resolve_instantiated_member(db, key, item, substitutor)
            else {
                return Ok(());
            };
            if !seen_keys.insert(key.clone()) {
                return Ok(());
            }
            visitor(relater, &key, &member_type)
        })?;
    } else {
        visit_member_items(db, &owner, |key, item| {
            if !seen_keys.insert(key.clone()) {
                return Ok(());
            }
            let Ok(member_type) = item.resolve_type(db) else {
                return Ok(());
            };
            visitor(relater, key, &member_type)
        })?;
    }

    if let Some(super_types) = db.get_type_index().get_super_types_iter(&type_id) {
        for super_type in super_types {
            let super_type = substitutor
                .as_ref()
                .map(|substitutor| instantiate_type_generic(db, super_type, substitutor))
                .unwrap_or_else(|| super_type.clone());
            visit_declared_type_members(relater, &super_type, seen_keys, visited_types, visitor)?;
        }
    }

    // 无父类型且无自身成员的 alias: 有效成员位于 alias origin.
    // alias substitutor 只在此处需要, 确认 is_alias && !has_supers 后再构造.
    if !has_supers
        && let Some(type_decl) = type_decl.as_ref()
        && type_decl.is_alias()
    {
        let alias_substitutor = generic_params.map(|generic_params| {
            TypeSubstitutor::from_alias(generic_params.to_vec(), type_id.clone())
        });
        if let Some(origin) = type_decl.get_alias_origin(db, alias_substitutor.as_ref()) {
            return visit_declared_type_members(
                relater,
                &origin,
                seen_keys,
                visited_types,
                visitor,
            );
        }
    }

    Ok(())
}

fn resolve_instantiated_member(
    db: &DbIndex,
    key: &LuaMemberKey,
    item: &LuaMemberIndexItem,
    substitutor: &TypeSubstitutor,
) -> Option<(LuaMemberKey, LuaType)> {
    let Ok(member_type) = item.resolve_type(db) else {
        return None;
    };
    let member_type = instantiate_type_generic(db, &member_type, substitutor);
    let mut key = key.clone();
    // 索引成员的键类型同样需要实例化, 否则泛型父类型的 [T] 无法收敛为实际键.
    if let LuaMemberKey::TypeKey(key_type) = &key {
        let instantiated_key = instantiate_type_generic(db, key_type, substitutor);
        if instantiated_key != *key_type {
            key = LuaMemberKey::TypeKey(instantiated_key);
        }
    }
    Some((key, member_type))
}
