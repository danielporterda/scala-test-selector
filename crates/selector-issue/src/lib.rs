use selector_types::{Error, IssueKind, Opcode, OperationId};

/// Actual transfer branch that reported uncertainty. These IDs are persisted;
/// no reason claims a source operation when the branch had none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum RuntimeIssueReason {
    MissingCallbackTarget = 1,
    UnknownCallbackValue = 2,
    IncompleteCallbackDispatch = 3,
    ExecutionGuard = 4,
    MissingExecutableBody = 5,
    UnboundCallbackTarget = 6,
    MissingFieldTarget = 7,
    UnknownFieldValue = 8,
    UnknownSuperOwner = 9,
    IncompleteVirtualDispatch = 10,
    MissingCallTarget = 11,
    UnknownOperation = 12,
    /// A callback may run, but scheduling and the Future result are unmodeled.
    IncompleteDeferredCallback = 13,
}
impl RuntimeIssueReason {
    pub fn decode(raw: u32) -> Result<Self, Error> {
        Ok(match raw {
            1 => Self::MissingCallbackTarget,
            2 => Self::UnknownCallbackValue,
            3 => Self::IncompleteCallbackDispatch,
            4 => Self::ExecutionGuard,
            5 => Self::MissingExecutableBody,
            6 => Self::UnboundCallbackTarget,
            7 => Self::MissingFieldTarget,
            8 => Self::UnknownFieldValue,
            9 => Self::UnknownSuperOwner,
            10 => Self::IncompleteVirtualDispatch,
            11 => Self::MissingCallTarget,
            12 => Self::UnknownOperation,
            13 => Self::IncompleteDeferredCallback,
            _ => return Err(Error::Invalid("runtime issue reason")),
        })
    }
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MissingCallbackTarget => "missing_callback_target",
            Self::UnknownCallbackValue => "unknown_callback_value",
            Self::IncompleteCallbackDispatch => "incomplete_callback_dispatch",
            Self::ExecutionGuard => "execution_guard",
            Self::MissingExecutableBody => "missing_executable_body",
            Self::UnboundCallbackTarget => "unbound_callback_target",
            Self::MissingFieldTarget => "missing_field_target",
            Self::UnknownFieldValue => "unknown_field_value",
            Self::UnknownSuperOwner => "unknown_super_owner",
            Self::IncompleteVirtualDispatch => "incomplete_virtual_dispatch",
            Self::MissingCallTarget => "missing_call_target",
            Self::UnknownOperation => "unknown_operation",
            Self::IncompleteDeferredCallback => "incomplete_deferred_callback",
        }
    }
    pub const fn kind(self) -> IssueKind {
        match self {
            Self::MissingCallbackTarget | Self::MissingFieldTarget | Self::MissingCallTarget => {
                IssueKind::UnresolvedSymbol
            }
            _ => IssueKind::UnknownExecution,
        }
    }
    pub const fn accepts_opcode(self, opcode: Opcode) -> bool {
        let call = matches!(
            opcode,
            Opcode::Call
                | Opcode::VirtualCall
                | Opcode::Initialize
                | Opcode::DefaultArgument
                | Opcode::RegisterTest
        );
        match self {
            Self::ExecutionGuard => true,
            Self::MissingExecutableBody => false,
            Self::MissingCallbackTarget
            | Self::UnknownCallbackValue
            | Self::IncompleteCallbackDispatch => call || matches!(opcode, Opcode::InvokeCallback),
            Self::UnboundCallbackTarget => matches!(opcode, Opcode::BindCallback),
            Self::MissingFieldTarget => matches!(opcode, Opcode::LoadField | Opcode::StoreField),
            Self::UnknownFieldValue => {
                matches!(opcode, Opcode::LoadField | Opcode::ReadElements) || call
            }
            Self::UnknownSuperOwner | Self::IncompleteVirtualDispatch | Self::MissingCallTarget => {
                call
            }
            Self::UnknownOperation => {
                matches!(
                    opcode,
                    Opcode::Unknown | Opcode::PackSequence | Opcode::StoreField
                ) || call
            }
            Self::IncompleteDeferredCallback => call,
        }
    }
}

/// One actual issue occurrence, independent of context/value pool ownership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RuntimeIssueSite {
    pub kind: IssueKind,
    pub operation: OperationId,
    pub reason: RuntimeIssueReason,
}
impl RuntimeIssueSite {
    /// Facts/graph owners separately validate the operation and its owning body.
    pub fn validate(self) -> Result<(), Error> {
        if self.kind != self.reason.kind()
            || (self.operation.is_none()
                && !matches!(
                    self.reason,
                    RuntimeIssueReason::ExecutionGuard | RuntimeIssueReason::MissingExecutableBody
                ))
            || (self.reason == RuntimeIssueReason::MissingExecutableBody
                && !self.operation.is_none())
        {
            return Err(Error::Invalid("runtime issue site"));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn reasons_round_trip_and_validate_actual_operation_requirements() {
        assert_eq!(std::mem::size_of::<RuntimeIssueSite>(), 12);
        for raw in 1..=13 {
            let reason = RuntimeIssueReason::decode(raw).unwrap();
            assert_eq!(reason as u32, raw);
            assert!(!reason.as_str().is_empty());
            let operation = if reason == RuntimeIssueReason::MissingExecutableBody {
                OperationId::NONE
            } else {
                OperationId(0)
            };
            let mut site = RuntimeIssueSite {
                kind: reason.kind(),
                operation,
                reason,
            };
            site.validate().unwrap();
            site.kind = IssueKind::InvalidInput;
            assert!(site.validate().is_err());
        }
        assert!(RuntimeIssueReason::decode(0).is_err());
        assert!(RuntimeIssueReason::decode(14).is_err());
        assert!(
            RuntimeIssueSite {
                kind: IssueKind::UnknownExecution,
                operation: OperationId::NONE,
                reason: RuntimeIssueReason::UnknownCallbackValue,
            }
            .validate()
            .is_err()
        );
    }

    #[test]
    fn incomplete_deferred_callback_requires_a_call_operation() {
        let reason = RuntimeIssueReason::IncompleteDeferredCallback;
        assert_eq!(reason.kind(), IssueKind::UnknownExecution);
        assert_eq!(reason.as_str(), "incomplete_deferred_callback");
        assert!(reason.accepts_opcode(Opcode::Call));
        assert!(reason.accepts_opcode(Opcode::VirtualCall));
        assert!(!reason.accepts_opcode(Opcode::InvokeCallback));
        assert!(!reason.accepts_opcode(Opcode::BindCallback));
        assert!(!reason.accepts_opcode(Opcode::Unknown));
        assert!(
            RuntimeIssueSite {
                kind: reason.kind(),
                operation: OperationId::NONE,
                reason,
            }
            .validate()
            .is_err()
        );
    }
}
