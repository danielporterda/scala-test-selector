//! Reviewed synchronous WordSpec protocol boundaries, separate from callback ABI.
//!
//! These pins authorize only the stated stateful/partial recipe. They do not
//! authorize an empty Engine constructor, application overrides, another style,
//! unknown registry escapes, or complete assertion/property-check semantics.
use selector_types::ContentHash;

pub const VERSION: &str = "scalatest-3.2.19/synchronous-wordspec-execution/1";
pub const WORDSPEC: &str = "org/scalatest/wordspec/AnyWordSpecLike";
pub const WORDSPEC_ARCHIVE: &str =
    "08050f3d05c72575cac29a1483185b443d5f9f34c1fcf80c683083330385ef93";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Recipe {
    Initialize,
    OpaqueEngineInput,
    Register { callback: u16 },
    Scope { callback: u16 },
    Names,
    Tags,
    TestData,
    Run,
    RunTests,
    RunTest,
}
#[derive(Clone, Copy, Debug)]
pub struct Contract {
    pub owner: &'static str,
    pub name: &'static str,
    pub descriptor: &'static str,
    pub flags: u16,
    pub class_sha256: &'static str,
    pub code_sha256: &'static str,
    pub recipe: Recipe,
}
impl Contract {
    /// All physical admission/provider checks precede this immutable pin check.
    pub fn matches(
        &self,
        archive: ContentHash,
        class: ContentHash,
        code: ContentHash,
        flags: u16,
    ) -> bool {
        flags == self.flags
            && ContentHash::from_hex(WORDSPEC_ARCHIVE).is_ok_and(|h| h == archive)
            && ContentHash::from_hex(self.class_sha256).is_ok_and(|h| h == class)
            && ContentHash::from_hex(self.code_sha256).is_ok_and(|h| h == code)
    }
}
pub fn lookup(owner: &str, name: &str, descriptor: &str) -> Option<&'static Contract> {
    CONTRACTS
        .iter()
        .find(|spec| (spec.owner, spec.name, spec.descriptor) == (owner, name, descriptor))
}
pub const CONTRACTS: &[Contract] = &[
    Contract {
        owner: WORDSPEC,
        name: "$anonfun$engine$1",
        descriptor: "()Ljava/lang/String;",
        flags: 4105,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "4b50819eaedc1190964c19aa9656b3492cc2a7fabf737e0f9d4069b688b81141",
        recipe: Recipe::OpaqueEngineInput,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "registerTestImpl",
        descriptor: "(Ljava/lang/String;Lscala/collection/immutable/Seq;Lscala/Function0;Lorg/scalactic/source/Position;)V",
        flags: 2,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "7e487347d85abfd38259c85c6433771ec4dcc1b761acb4a58d85c9b68ef802c2",
        recipe: Recipe::Register { callback: 2 },
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "registerIgnoredTestImpl",
        descriptor: "(Ljava/lang/String;Lscala/collection/immutable/Seq;Lscala/Function0;Lorg/scalactic/source/Position;)V",
        flags: 2,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "f4ce808b65fda9698c170bcf060c0d15094a7cc19b30d7a741d9c14727108472",
        recipe: Recipe::Register { callback: 2 },
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "org$scalatest$wordspec$AnyWordSpecLike$$registerTestToRun",
        descriptor: "(Ljava/lang/String;Lscala/collection/immutable/List;Ljava/lang/String;Lscala/Function0;Lorg/scalactic/source/Position;)V",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "3ad1f0b6fc9c91fa4e6f81c53c0a7264b3f6fe93865a408e0c2082e56fcefc6e",
        recipe: Recipe::Register { callback: 3 },
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "org$scalatest$wordspec$AnyWordSpecLike$$registerBranch",
        descriptor: "(Ljava/lang/String;Lscala/Option;Ljava/lang/String;Ljava/lang/String;IILorg/scalactic/source/Position;Lscala/Function0;)V",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "dbf2e5018cb86772eee811447851c07d4202a468d04f5eb2a96736983c7ed375",
        recipe: Recipe::Scope { callback: 7 },
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "tags",
        descriptor: "()Lscala/collection/immutable/Map;",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "db5bf41bb3315c07bcfc9fd7f401fbae4d3da1c7ecb05f2b0429f7b48df16497",
        recipe: Recipe::Tags,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "runTest",
        descriptor: "(Ljava/lang/String;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "ca6d82e6349a542d8443322a690eb8e6bc16758176ef431cbbeb5d3ed809b392",
        recipe: Recipe::RunTest,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "runTests",
        descriptor: "(Lscala/Option;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "42658e73eab7c9069ec016c36be45dbd34b0da4e738778ec4b9eff64a122b5a9",
        recipe: Recipe::RunTests,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "testNames",
        descriptor: "()Lscala/collection/immutable/Set;",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "7f3bb90616a9dca93b3eb3dd08a685c225fafe08bfc418211bed4f9fc56905f0",
        recipe: Recipe::Names,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "run",
        descriptor: "(Lscala/Option;Lorg/scalatest/Args;)Lorg/scalatest/Status;",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "460b0615f983089c71dd0733d91cdc987a5d1922578a2db2137e190d8bbb97d7",
        recipe: Recipe::Run,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "testDataFor",
        descriptor: "(Ljava/lang/String;Lorg/scalatest/ConfigMap;)Lorg/scalatest/TestData;",
        flags: 1,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "a8bf3914ce54de34fc3aff49918d9f68bf778b750a7f8c74a74b90800604bb24",
        recipe: Recipe::TestData,
    },
    Contract {
        owner: "org/scalatest/wordspec/AnyWordSpecLike",
        name: "$init$",
        descriptor: "(Lorg/scalatest/wordspec/AnyWordSpecLike;)V",
        flags: 9,
        class_sha256: "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af",
        code_sha256: "a821b39698acb6b1aaee81792f214b818521bc7fec8a1462ad966a8ae76edc01",
        recipe: Recipe::Initialize,
    },
];

/// Logical accessor storage is explicit model state, not a JVM backing field.
pub const ACCESSOR_NAMESPACE: &str = "@selector:accessor:org/scalatest/wordspec/AnyWordSpecLike:";
pub const WORDSPEC_CLASS_SHA256: &str =
    "89aefea679450680f3100e16ef5a4f4ec0758c6728eeb703fa87c23e059c13af";
#[derive(Clone, Copy, Debug)]
pub struct Accessor {
    pub owner: &'static str,
    pub getter: &'static str,
    pub setter: &'static str,
    pub value_descriptor: &'static str,
    pub slot: &'static str,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AccessorKind {
    Get,
    Set,
}
pub fn accessor(
    owner: &str,
    name: &str,
    descriptor: &str,
) -> Option<(&'static Accessor, AccessorKind)> {
    ACCESSORS.iter().find_map(|spec| {
        if spec.owner != owner {
            return None;
        }
        if name == spec.getter && descriptor.strip_prefix("()") == Some(spec.value_descriptor) {
            Some((spec, AccessorKind::Get))
        } else if name == spec.setter
            && descriptor
                .strip_prefix('(')
                .and_then(|s| s.strip_suffix(")V"))
                == Some(spec.value_descriptor)
        {
            Some((spec, AccessorKind::Set))
        } else {
            None
        }
    })
}
pub const ACCESSORS: &[Accessor] = &[
    Accessor {
        owner: WORDSPEC,
        getter: "org$scalatest$wordspec$AnyWordSpecLike$$engine",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$org$scalatest$wordspec$AnyWordSpecLike$$engine_$eq",
        value_descriptor: "Lorg/scalatest/Engine;",
        slot: "org$scalatest$wordspec$AnyWordSpecLike$$engine",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "stackDepth",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$stackDepth_$eq",
        value_descriptor: "I",
        slot: "stackDepth",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "it",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$it_$eq",
        value_descriptor: "Lorg/scalatest/wordspec/AnyWordSpecLike$ItWord;",
        slot: "it",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "they",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$they_$eq",
        value_descriptor: "Lorg/scalatest/wordspec/AnyWordSpecLike$TheyWord;",
        slot: "they",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "subjectRegistrationFunction",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$subjectRegistrationFunction_$eq",
        value_descriptor: "Lorg/scalatest/verbs/StringVerbBlockRegistration;",
        slot: "subjectRegistrationFunction",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "subjectWithAfterWordRegistrationFunction",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$subjectWithAfterWordRegistrationFunction_$eq",
        value_descriptor: "Lorg/scalatest/verbs/SubjectWithAfterWordRegistration;",
        slot: "subjectWithAfterWordRegistrationFunction",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "behave",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$behave_$eq",
        value_descriptor: "Lorg/scalatest/verbs/BehaveWord;",
        slot: "behave",
    },
    Accessor {
        owner: WORDSPEC,
        getter: "styleName",
        setter: "org$scalatest$wordspec$AnyWordSpecLike$_setter_$styleName_$eq",
        value_descriptor: "Ljava/lang/String;",
        slot: "styleName",
    },
];

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn exact_accessor_pairs_use_one_slot_without_name_heuristics() {
        assert_eq!(ACCESSORS.len(), 8);
        for (i, spec) in ACCESSORS.iter().enumerate() {
            let getter = format!("(){}", spec.value_descriptor);
            let setter = format!("({})V", spec.value_descriptor);
            let (g, kind) = accessor(spec.owner, spec.getter, &getter).unwrap();
            assert_eq!(kind, AccessorKind::Get);
            let (s, kind) = accessor(spec.owner, spec.setter, &setter).unwrap();
            assert_eq!(kind, AccessorKind::Set);
            assert_eq!(g.slot, s.slot);
            assert!(
                ACCESSORS[i + 1..]
                    .iter()
                    .all(|other| other.slot != spec.slot)
            );
            for descriptor in [
                "()V",
                "(Ljava/lang/Object;)V",
                "()Ljava/lang/Object;",
                "(I)Ljava/lang/Object;",
            ] {
                if descriptor != getter {
                    assert!(accessor(spec.owner, spec.getter, descriptor).is_none());
                }
            }
            assert!(accessor("example/AnyWordSpecLike", spec.getter, &getter).is_none());
            assert!(accessor(spec.owner, "getSubjectRegistrationFunction", &getter).is_none());
        }
    }
    #[test]
    fn engine_protocol_has_exact_code_pins_and_does_not_cover_other_styles_or_engine_constructor() {
        for spec in CONTRACTS {
            let archive = ContentHash::from_hex(WORDSPEC_ARCHIVE).unwrap();
            let class = ContentHash::from_hex(spec.class_sha256).unwrap();
            let code = ContentHash::from_hex(spec.code_sha256).unwrap();
            assert!(spec.matches(archive, class, code, spec.flags));
            assert!(!spec.matches(ContentHash([7; 32]), class, code, spec.flags));
            assert!(!spec.matches(archive, ContentHash([8; 32]), code, spec.flags));
            assert!(!spec.matches(archive, class, ContentHash([9; 32]), spec.flags));
            assert!(!spec.matches(archive, class, code, spec.flags ^ 8));
            assert!(
                lookup(
                    "org/scalatest/wordspec/FixtureAnyWordSpecLike",
                    spec.name,
                    spec.descriptor
                )
                .is_none()
            );
            assert!(
                lookup(
                    "org/scalatest/wordspec/AsyncWordSpecLike",
                    spec.name,
                    spec.descriptor
                )
                .is_none()
            );
        }
        assert!(
            lookup(
                "org/scalatest/Engine",
                "<init>",
                "(Lscala/Function0;Ljava/lang/String;)V"
            )
            .is_none()
        );
        assert!(lookup(WORDSPEC, "getEngine", "()Lorg/scalatest/Engine;").is_none());
    }
}
