use crate::LuaType;

use super::fast_eq_check;

#[inline(always)]
pub(super) fn is_simple_assignable(source: &LuaType, target: &LuaType) -> Option<bool> {
    if fast_eq_check(source, target) {
        return Some(true);
    }

    let (can_reject_simple_target_early, related) = match source {
        LuaType::Unknown => return Some(true),
        LuaType::Boolean => (
            true,
            matches!(target, LuaType::Boolean | LuaType::BooleanConst(_)),
        ),
        LuaType::BooleanConst(source_value) | LuaType::DocBooleanConst(source_value) => (
            true,
            matches!(target, LuaType::Boolean | LuaType::BooleanConst(_))
                || matches!(target, LuaType::DocBooleanConst(target_value) if source_value == target_value),
        ),
        LuaType::String => (
            true,
            matches!(target, LuaType::String | LuaType::StringConst(_))
                || matches!(target, LuaType::StrTplRef(_) | LuaType::Language(_)),
        ),
        LuaType::StringConst(source_value) | LuaType::DocStringConst(source_value) => (
            true,
            matches!(target, LuaType::String | LuaType::StringConst(_))
                || matches!(target, LuaType::DocStringConst(target_value) if source_value == target_value)
                || matches!(target, LuaType::StrTplRef(_) | LuaType::Language(_)),
        ),
        LuaType::StrTplRef(_) => (
            true,
            matches!(target, LuaType::String | LuaType::StringConst(_)) || source == target,
        ),
        LuaType::Language(source_language) => (
            true,
            matches!(
                target,
                LuaType::String | LuaType::StringConst(_) | LuaType::StrTplRef(_)
            ) || matches!(target, LuaType::Language(target_language) if source_language == target_language),
        ),
        LuaType::Integer => (
            true,
            matches!(
                target,
                LuaType::Integer
                    | LuaType::IntegerConst(_)
                    | LuaType::Number
                    | LuaType::FloatConst(_)
            ),
        ),
        LuaType::IntegerConst(source_value) | LuaType::DocIntegerConst(source_value) => (
            true,
            matches!(
                target,
                LuaType::Integer
                    | LuaType::IntegerConst(_)
                    | LuaType::Number
                    | LuaType::FloatConst(_)
            ) || matches!(target, LuaType::DocIntegerConst(target_value) if source_value == target_value),
        ),
        LuaType::Number | LuaType::FloatConst(_) => (
            true,
            matches!(target, LuaType::Number | LuaType::FloatConst(_)),
        ),
        LuaType::Nil => (true, matches!(target, LuaType::Nil)),
        LuaType::Table => (true, matches!(target, LuaType::Table)),
        LuaType::Userdata => (true, matches!(target, LuaType::Table | LuaType::Userdata)),
        LuaType::Function => (true, matches!(target, LuaType::Function)),
        LuaType::Thread => (true, matches!(target, LuaType::Thread)),
        LuaType::Io => (true, matches!(target, LuaType::Io)),
        LuaType::Global => (true, matches!(target, LuaType::Table | LuaType::Global)),
        LuaType::Namespace(source_namespace) => (
            true,
            matches!(
                target,
                LuaType::Namespace(target_namespace) if source_namespace == target_namespace
            ),
        ),
        LuaType::DocFunction(_) | LuaType::Signature(_) => {
            (false, matches!(target, LuaType::Function))
        }
        _ => (false, false),
    };

    if related {
        return Some(true);
    }

    // source 可在入口阶段失败简单目标
    match target {
        LuaType::Nil
        | LuaType::Table
        | LuaType::Userdata
        | LuaType::Function
        | LuaType::Thread
        | LuaType::Io
        | LuaType::Global
        | LuaType::Namespace(_)
        | LuaType::Boolean
        | LuaType::BooleanConst(_)
        | LuaType::String
        | LuaType::StringConst(_)
        | LuaType::Integer
        | LuaType::IntegerConst(_)
        | LuaType::Number
        | LuaType::FloatConst(_)
        | LuaType::DocStringConst(_)
        | LuaType::DocIntegerConst(_)
        | LuaType::DocBooleanConst(_)
        | LuaType::StrTplRef(_)
        | LuaType::Language(_)
            if can_reject_simple_target_early =>
        {
            Some(false)
        }
        _ => None,
    }
}
