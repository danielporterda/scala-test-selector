//! Explicit external ABI contracts over complete compiler symbols. These prove
//! argument deferral/callback policy, never complete library execution effects.
//! Declared compiler parameter modes always take precedence over this fallback.
pub mod native_abi;
pub mod scalatest_execution;
use selector_types::symbol::{global_owner, member_name};

pub const VERSION: &str = "scalatest-3.2.19/registration-abi-v3:pinned-native-bindings";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalaTestCall {
    Registration,
    Scope,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DeferredArgument {
    pub kind: ScalaTestCall,
    pub clause: u32,
    pub argument: u32,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CallbackArgument {
    pub kind: ScalaTestCall,
    pub clause: u32,
    pub argument: u32,
    /// False means evaluate the argument expression during registration, then
    /// execute the function value it returns as the registered test.
    pub by_name: bool,
}
// SemanticDB method disambiguators are part of the exact method identity. Do
// not reinterpret malformed descriptors or type/value parameters as a method.
fn overload(symbol: &str, owner: &str, name: &str) -> Option<Option<u32>> {
    let suffix = symbol.strip_prefix(owner)?.strip_prefix(name)?;
    if suffix == "()." {
        return Some(None);
    }
    let digits = suffix.strip_prefix("(+")?.strip_suffix(").")?;
    if digits.is_empty() || digits.starts_with('0') || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some(Some(digits.parse().ok()?))
}
pub fn scalatest_callback_argument(symbol: &str) -> Option<CallbackArgument> {
    let owner = global_owner(symbol)?;
    let name = member_name(symbol)?;
    let overloaded = overload(symbol, owner, name)?;
    let mut by_name = true;
    let (kind, clause) = match (owner, name) {
        (
            "org/scalatest/funsuite/AnyFunSuiteLike#",
            "test" | "ignore" | "registerTest" | "registerIgnoredTest",
        ) if overloaded.is_none() => (ScalaTestCall::Registration, 1),
        // Actual 3.2.19 compiler overload taking the WordSpec by-name scope.
        ("org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#", "should")
            if overloaded == Some(2) =>
        {
            (ScalaTestCall::Scope, 0)
        }
        (
            "org/scalatest/flatspec/AnyFlatSpecLike#ItVerbString#"
            | "org/scalatest/flatspec/AnyFlatSpecLike#InAndIgnoreMethods#",
            "in" | "ignore",
        ) if overloaded.is_none() => (ScalaTestCall::Registration, 0),
        _ => {
            let word = owner.strip_prefix("org/scalatest/wordspec/")?;
            let (style, wrapper) = word.split_once('#')?;
            let fixture = match style {
                "AnyWordSpecLike" | "AsyncWordSpecLike" => false,
                "FixtureAnyWordSpecLike" | "FixtureAsyncWordSpecLike" => true,
                _ => return None,
            };
            if !matches!(
                wrapper,
                "WordSpecStringWrapper#" | "ResultOfTaggedAsInvocationOnString#"
            ) {
                return None;
            }
            match name {
                "in" | "ignore" if fixture && matches!(overloaded, None | Some(1)) => {
                    by_name = false;
                    (ScalaTestCall::Registration, 0)
                }
                "in" | "ignore" | "is" if overloaded.is_none() => (ScalaTestCall::Registration, 0),
                "when" | "that" | "which"
                    if wrapper == "WordSpecStringWrapper#" && overloaded.is_none() =>
                {
                    (ScalaTestCall::Scope, 0)
                }
                _ => return None,
            }
        }
    };
    Some(CallbackArgument {
        kind,
        clause,
        argument: 0,
        by_name,
    })
}

pub fn scalatest_deferred_argument(symbol: &str) -> Option<DeferredArgument> {
    let callback = scalatest_callback_argument(symbol)?;
    callback.by_name.then_some(DeferredArgument {
        kind: callback.kind,
        clause: callback.clause,
        argument: callback.argument,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_supported_abi_preserves_clause_and_overload_boundaries() {
        for symbol in ["org/scalatest/funsuite/AnyFunSuiteLike#test()."] {
            assert_eq!(
                scalatest_deferred_argument(symbol),
                Some(DeferredArgument {
                    kind: ScalaTestCall::Registration,
                    clause: 1,
                    argument: 0
                })
            );
        }
        assert_eq!(
            scalatest_deferred_argument(
                "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+2)."
            ),
            Some(DeferredArgument {
                kind: ScalaTestCall::Scope,
                clause: 0,
                argument: 0
            })
        );
        for symbol in [
            "example/AnyFunSuiteLike#test().",
            "org/scalatest/funsuite/Fake#test().",
            "org/scalatest/funsuite/AnyFunSuiteLike#test.",
            "org/scalatest/funsuite/AnyFunSuiteLike#test().(body)",
            "org/scalatest/funsuite/AnyFunSuiteLike#test(bad).",
            "org/scalatest/funsuite/AnyFunSuiteLike#test(+0).",
            "org/scalatest/funsuite/AnyFunSuiteLike#test(+1).",
            "org/scalatest/funsuite/AnyFunSuiteLike#test(+01).",
            "org/scalatest/funsuite/AnyFunSuiteLike#test(+4294967296).",
            "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should().",
            "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+1).",
        ] {
            assert_eq!(scalatest_deferred_argument(symbol), None, "{symbol}");
        }
    }
    #[test]
    fn fixture_function_values_are_distinct_from_async_by_name_and_scope_bodies() {
        for style in ["FixtureAnyWordSpecLike", "FixtureAsyncWordSpecLike"] {
            for wrapper in [
                "WordSpecStringWrapper",
                "ResultOfTaggedAsInvocationOnString",
            ] {
                for suffix in ["().", "(+1)."] {
                    let symbol = format!("org/scalatest/wordspec/{style}#{wrapper}#in{suffix}");
                    assert_eq!(
                        scalatest_callback_argument(&symbol).map(|c| c.by_name),
                        Some(false),
                        "{symbol}"
                    );
                    assert_eq!(scalatest_deferred_argument(&symbol), None);
                }
                assert_eq!(
                    scalatest_callback_argument(&format!(
                        "org/scalatest/wordspec/{style}#{wrapper}#in(+2)."
                    )),
                    None
                );
            }
        }
        for symbol in [
            "org/scalatest/wordspec/AsyncWordSpecLike#WordSpecStringWrapper#in().",
            "org/scalatest/wordspec/AsyncWordSpecLike#ResultOfTaggedAsInvocationOnString#in().",
            "org/scalatest/flatspec/AnyFlatSpecLike#ItVerbString#in().",
            "org/scalatest/wordspec/FixtureAnyWordSpecLike#WordSpecStringWrapper#is().",
            "org/scalatest/wordspec/AnyWordSpecLike#WordSpecStringWrapper#when().",
        ] {
            assert!(scalatest_deferred_argument(symbol).is_some(), "{symbol}");
        }
    }
}
