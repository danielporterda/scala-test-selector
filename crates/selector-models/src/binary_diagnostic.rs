//! Narrow structural validation for diagnostic tools. No admission or omission authority.
//!
//! This adapter borrows an already parsed class and reuses the existing checked
//! decoder. It does not establish JVM stack/type validity, effects, or providers.
use super::*;

/// Reusable instruction-boundary scratch; owns no class bytes.
#[derive(Default)]
pub struct CodeValidator {
    inner: super::envelope::StructuralCodeValidator,
}
impl CodeValidator {
    pub fn validate(
        &mut self,
        class: &ClassFile<'_>,
        method: &MethodInfo<'_>,
        limits: Limits,
    ) -> Result<()> {
        self.inner.validate(class, method, limits)
    }
    pub fn instruction_count(&self) -> usize {
        self.inner.instruction_count()
    }
    pub fn instruction_start(&self, pc: usize) -> bool {
        self.inner.instruction_start(pc)
    }
}
/// Borrow a checked UTF8 constant without exposing the constant-pool representation.
pub fn utf8<'a>(class: &ClassFile<'a>, index: u16) -> Result<&'a str> {
    class.utf(index)
}
fn bad(offset: usize) -> BinaryError {
    BinaryError::at(ErrorKind::BadConstant, offset)
}
/// Validate every constant, including unused references. Unknown attribute
/// payloads remain opaque; this is not a complete JVM verifier.
pub fn validate_constant_pool(class: &ClassFile<'_>) -> Result<()> {
    if !(45..=65).contains(&class.major) {
        return Err(BinaryError::at(ErrorKind::UnsupportedClassVersion, 6));
    }
    for (index, value) in class.pool.iter().enumerate().skip(1) {
        match *value {
            Constant::Utf8(_) => {
                if class.utf(index as u16)?.as_bytes().contains(&0) {
                    return Err(BinaryError::at(ErrorKind::InvalidUtf8, index));
                }
            }
            Constant::Class(_) => {
                let name = class.class(index as u16)?;
                if name.starts_with('[') {
                    field_descriptor(name)?;
                } else {
                    valid_class_name(name)?;
                }
            }
            Constant::String(text) => {
                class.utf(text)?;
            }
            Constant::Pair { name, descriptor } => {
                let name = class.utf(name)?;
                let descriptor = class.utf(descriptor)?;
                if descriptor.starts_with('(') {
                    method_descriptor(descriptor)?;
                } else {
                    field_descriptor(descriptor)?;
                }
                if !matches!(name, "<init>" | "<clinit>") {
                    valid_dynamic_name(name)?;
                }
            }
            Constant::Member { tag, .. } => {
                let member = class.member(index as u16, tag == 9)?;
                if tag == 9 {
                    field_descriptor(member.descriptor)?;
                } else {
                    method_descriptor(member.descriptor)?;
                }
                if member.name == "<clinit>"
                    || (member.name == "<init>"
                        && (tag != 10 || method_descriptor(member.descriptor)?.return_type != "V"))
                {
                    return Err(bad(index));
                }
                if !matches!(member.name, "<init>" | "<clinit>") {
                    valid_dynamic_name(member.name)?;
                }
            }
            // The parser already validates handles, dynamic constants and all
            // bootstrap rows, including unused ones, without recursive descent.
            Constant::Other => return Err(BinaryError::at(ErrorKind::UnsupportedConstant, index)),
            _ => {}
        }
    }
    Ok(())
}
