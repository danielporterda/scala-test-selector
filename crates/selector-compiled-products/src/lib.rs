//! New retained-Zinc source/product correspondence. Not execution authority.
mod classfile;
mod compiled_products;
pub use compiled_products::*;
/// Validated standard classfile attribution metadata, not a standalone source
/// ownership or effect-completeness certificate. Missing attributes stay None.
pub fn class_source_file(bytes: &[u8]) -> Result<Option<String>, Error> {
    Ok(classfile::parse(bytes)?.source_file)
}
#[cfg(test)]
mod source_file_tests {
    #[test]
    fn genuine_attribution_missing_metadata_and_malformed_bytes_remain_distinct() {
        let bytes = include_bytes!(
            "../../../fixtures/native-admission-chain/classes/admissioncase/Getter.class"
        );
        assert_eq!(
            super::class_source_file(bytes).unwrap().as_deref(),
            Some("Fixture.java")
        );
        let mut missing = bytes.to_vec();
        let at = missing
            .windows(10)
            .position(|s| s == b"SourceFile")
            .unwrap();
        missing[at + 9] = b'd';
        assert_eq!(super::class_source_file(&missing).unwrap(), None);
        assert!(super::class_source_file(&bytes[..8]).is_err());
    }
}
#[cfg(test)]
mod tests;
