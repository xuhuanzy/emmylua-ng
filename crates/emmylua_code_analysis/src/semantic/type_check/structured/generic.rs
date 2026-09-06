use crate::{LuaGenericType, LuaType};

use super::super::relation::{IntersectionState, Relater, RelationFailure, RelationResult};

/// 同族泛型先比较实参, 返回 None 时仍需成员检查或别名展开来验证方差.
pub(super) fn relate_same_family_generic_args(
    relater: &mut Relater,
    source_generic: &LuaGenericType,
    target_generic: &LuaGenericType,
    intersection_state: IntersectionState,
) -> Option<RelationResult> {
    let source_params = source_generic.get_params();
    let target_params = target_generic.get_params();
    if source_params.len() != target_params.len() {
        return None;
    }
    let mut all_trivial = true;
    for (source_param, target_param) in source_params.iter().zip(target_params) {
        // 判定一对类型是否在任意方差位置都可互换, 不能用 `fast_eq_check`, 其在逆变位置会误放行.
        let trivial = source_param == target_param
            || matches!(source_param, LuaType::Any | LuaType::SelfInfer)
            || matches!(
                target_param,
                LuaType::Any | LuaType::Unknown | LuaType::SelfInfer
            )
            || matches!(source_param, LuaType::TplRef(tpl) if tpl.get_constraint().is_none())
            || matches!(target_param, LuaType::TplRef(tpl) if tpl.get_constraint().is_none());
        all_trivial &= trivial;
        if !trivial {
            match relater.relate(source_param, target_param, intersection_state) {
                Err(RelationFailure::Indeterminate(kind)) => {
                    return Some(Err(RelationFailure::Indeterminate(kind)));
                }
                Err(RelationFailure::Unrelated) => return None,
                Ok(()) => {}
            }
        }
    }

    all_trivial.then_some(Ok(()))
}
