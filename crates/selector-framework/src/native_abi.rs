//! Versioned compiler/JVM identity bindings, separate from execution models.
//! Both the admitted archive and selected class bytes must match the reviewed
//! release; a compiler overload suffix is never a method-list ordinal.
use selector_types::ContentHash;

pub const SCALATEST_CORE_3_2_19: ContentHash = ContentHash([
    0x30, 0x23, 0x00, 0x81, 0xd0, 0x29, 0xf6, 0x34, 0x1b, 0x83, 0xfe, 0x7f, 0x15, 0x7d, 0x33, 0x61,
    0x13, 0xe1, 0xc9, 0x74, 0x97, 0xfe, 0x95, 0x01, 0x69, 0x29, 0x3d, 0x28, 0xa5, 0xbf, 0x29, 0x36,
]);
pub const SHOULD_WRAPPER_CLASS: ContentHash = ContentHash([
    0x18, 0x8a, 0xee, 0xe8, 0x88, 0x5a, 0x05, 0x6a, 0xa2, 0x3c, 0xd4, 0x67, 0x3b, 0xc7, 0x44, 0x1a,
    0xf6, 0xab, 0xc1, 0xfc, 0x9e, 0xef, 0x20, 0xae, 0x47, 0xdc, 0xe2, 0x21, 0x6e, 0x9a, 0x35, 0xc0,
]);

pub const SHOULD_SCOPE_SYMBOL: &str =
    "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+2).";
pub const SHOULD_WRAPPER_OWNER: &str = "org/scalatest/verbs/ShouldVerb$StringShouldWrapperForVerb";
pub const SHOULD_SCOPE_DESCRIPTOR: &str =
    "(Lscala/Function0;Lorg/scalatest/verbs/StringVerbBlockRegistration;)V";

/// Supplies only an exact missing compiler/JVM binding. Callers still parse the
/// selected class and lower the real matching method, retaining every effect and
/// uncertainty boundary. Existing compiler signatures take precedence.
pub fn admitted_method_descriptor(
    compiler_symbol: &str,
    jvm_owner: &str,
    jvm_name: &str,
    archive_hash: ContentHash,
    class_hash: ContentHash,
) -> Option<&'static str> {
    (compiler_symbol == SHOULD_SCOPE_SYMBOL
        && jvm_owner == SHOULD_WRAPPER_OWNER
        && jvm_name == "should"
        && archive_hash == SCALATEST_CORE_3_2_19
        && class_hash == SHOULD_WRAPPER_CLASS)
        .then_some(SHOULD_SCOPE_DESCRIPTOR)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_release_owner_symbol_and_both_hashes_are_required() {
        let lookup = |symbol, owner, name, archive, class| {
            admitted_method_descriptor(symbol, owner, name, archive, class)
        };
        assert_eq!(
            lookup(
                SHOULD_SCOPE_SYMBOL,
                SHOULD_WRAPPER_OWNER,
                "should",
                SCALATEST_CORE_3_2_19,
                SHOULD_WRAPPER_CLASS
            ),
            Some(SHOULD_SCOPE_DESCRIPTOR)
        );
        for symbol in [
            "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should().",
            "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+1).",
            "org/scalatest/verbs/ShouldVerb#StringShouldWrapperForVerb#should(+3).",
            "user/ShouldVerb#StringShouldWrapperForVerb#should(+2).",
        ] {
            assert_eq!(
                lookup(
                    symbol,
                    SHOULD_WRAPPER_OWNER,
                    "should",
                    SCALATEST_CORE_3_2_19,
                    SHOULD_WRAPPER_CLASS
                ),
                None
            );
        }
        assert_eq!(
            lookup(
                SHOULD_SCOPE_SYMBOL,
                "shadow/Wrapper",
                "should",
                SCALATEST_CORE_3_2_19,
                SHOULD_WRAPPER_CLASS
            ),
            None
        );
        assert_eq!(
            lookup(
                SHOULD_SCOPE_SYMBOL,
                SHOULD_WRAPPER_OWNER,
                "should$",
                SCALATEST_CORE_3_2_19,
                SHOULD_WRAPPER_CLASS
            ),
            None
        );
        assert_eq!(
            lookup(
                SHOULD_SCOPE_SYMBOL,
                SHOULD_WRAPPER_OWNER,
                "should",
                ContentHash::default(),
                SHOULD_WRAPPER_CLASS
            ),
            None
        );
        assert_eq!(
            lookup(
                SHOULD_SCOPE_SYMBOL,
                SHOULD_WRAPPER_OWNER,
                "should",
                SCALATEST_CORE_3_2_19,
                ContentHash::default()
            ),
            None
        );
    }
}
