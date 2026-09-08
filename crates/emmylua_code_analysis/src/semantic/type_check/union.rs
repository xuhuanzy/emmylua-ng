use std::borrow::Cow;

use crate::{
    LuaMemberKey, LuaType, LuaUnionType, semantic::type_check::error_chain::not_assignable_message,
};

use super::{
    relation::{IntersectionState, Relater, RelationFailure, RelationResult},
    structured::{collect_missing_members, unrelated_missing_members},
};

pub(crate) fn relate_union(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> Option<RelationResult> {
    if let LuaType::Union(source_union) = source {
        let result =
            relate_source_union_members(relater, source_union.iter(), target, intersection_state);
        return Some(relater.on_unrelated(result, |db| not_assignable_message(db, source, target)));
    }
    let LuaType::Union(target_union) = target else {
        return None;
    };

    // 源确定非空时, 单一可空目标可直接剥离为其非 Nil 成员进行比对.
    if !source.is_nullable()
        && let Some(non_nil_target) = get_single_non_nil_candidate(target_union)
    {
        return Some(relater.relate(source, &non_nil_target, intersection_state));
    }
    Some(relate_to_target_union_candidates(
        relater,
        source,
        target,
        target_union.iter(),
        intersection_state,
    ))
}

fn get_single_non_nil_candidate(target: &LuaUnionType) -> Option<Cow<'_, LuaType>> {
    let mut has_nil = false;
    let mut non_nil = None;
    for candidate in target.iter() {
        if candidate.is_nil() {
            has_nil = true;
        } else if non_nil.is_some()
            || matches!(
                candidate.as_ref(),
                LuaType::Union(_) | LuaType::MultiLineUnion(_)
            )
        {
            return None;
        } else {
            non_nil = Some(candidate);
        }
    }
    has_nil.then_some(non_nil).flatten()
}

fn relate_source_union_members<'a>(
    relater: &mut Relater,
    members: impl Iterator<Item = Cow<'a, LuaType>>,
    target: &LuaType,
    intersection_state: IntersectionState,
) -> RelationResult {
    let mut first_indeterminate = None;
    for member in members {
        match relater.probe_relation(&member, target, intersection_state) {
            Ok(()) => {}
            Err(RelationFailure::Indeterminate(kind)) => {
                first_indeterminate.get_or_insert(kind);
            }
            Err(RelationFailure::Unrelated) => {
                if !relater.is_explain() {
                    return Err(RelationFailure::Unrelated);
                }
                return relater.relate(&member, target, intersection_state);
            }
        }
    }
    if let Some(kind) = first_indeterminate {
        return Err(RelationFailure::Indeterminate(kind));
    }
    Ok(())
}

fn relate_to_target_union_candidates<'a>(
    relater: &mut Relater,
    source: &LuaType,
    target: &LuaType,
    candidates: impl Iterator<Item = Cow<'a, LuaType>>,
    intersection_state: IntersectionState,
) -> RelationResult {
    let mut indeterminate = None;
    let mut failed_candidates = Vec::new();

    for candidate in candidates {
        match relater.probe_relation(source, &candidate, intersection_state) {
            Ok(()) => return Ok(()),
            Err(RelationFailure::Indeterminate(kind)) => {
                indeterminate.get_or_insert(kind);
            }
            Err(RelationFailure::Unrelated) => {}
        }
        if relater.is_explain() {
            failed_candidates.push(candidate.into_owned());
        }
    }

    if let Some(kind) = indeterminate {
        return Err(RelationFailure::Indeterminate(kind));
    }

    if !relater.is_explain() {
        return Err(RelationFailure::Unrelated);
    }

    // probe_relation 有早退行为, 因此得到的结果并不一定是最匹配的, 我们必须独立处理缺失字段判别.
    let mut evidence: Option<(usize, Vec<LuaMemberKey>)> = None;
    for (index, candidate) in failed_candidates.iter().enumerate() {
        let (missing_keys, has_shared_key) =
            collect_missing_members(relater, source, candidate, intersection_state)?;
        if !has_shared_key {
            continue;
        }
        if missing_keys.is_empty() {
            // 必填字段全部在场: 失败必然是字段类型不匹配, 重放该分支取路径化证据.
            evidence = Some((index, missing_keys));
            break;
        }
        if evidence
            .as_ref()
            .is_none_or(|(_, best_missing)| missing_keys.len() < best_missing.len())
        {
            evidence = Some((index, missing_keys));
        }
    }

    let Some((best_index, missing_keys)) = evidence else {
        return relater.fail(|db| not_assignable_message(db, source, target));
    };
    if !missing_keys.is_empty() {
        return unrelated_missing_members(
            relater,
            source,
            &failed_candidates[best_index],
            missing_keys,
        );
    }
    relater.relate(source, &failed_candidates[best_index], intersection_state)
}
