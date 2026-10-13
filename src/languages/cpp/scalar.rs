//! Scalar interpretation for the pinned C++ target. Clang retains promotions as
//! explicit typed casts; this module does not infer C++ types from syntax.
use super::CppType;
use crate::kernel;
use crate::kernel::{CExpression, CType, MachineIntegerConstant, MachineIntegerType};
use crate::languages::c::syntax::{C0Type, LongRank};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ScalarKind {
    Bool,
    UInt8,
    Int32,
    Int64,
    UInt32,
    UInt64,
    Int128,
    UInt128,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct Scalar {
    pub kind: ScalarKind,
    pub is_const: bool,
}

impl Scalar {
    pub fn of(value: &CppType) -> Option<Self> {
        let (kind, is_const) = match value {
            CppType::Enumeration {
                is_scoped: true,
                is_fixed: true,
                underlying_type,
                is_const,
                ..
            } if matches!(
                underlying_type.as_ref(),
                CppType::Integer {
                    bits: 8,
                    signed: false,
                    is_const: false,
                    ..
                }
            ) =>
            {
                (ScalarKind::UInt8, *is_const)
            }
            CppType::Boolean { bits: 8, is_const } => (ScalarKind::Bool, *is_const),
            CppType::Integer {
                bits,
                signed,
                is_const,
                ..
            } => (
                match (*bits, *signed) {
                    (8, false) => ScalarKind::UInt8,
                    (32, true) => ScalarKind::Int32,
                    (64, true) => ScalarKind::Int64,
                    (32, false) => ScalarKind::UInt32,
                    (64, false) => ScalarKind::UInt64,
                    (128, true) => ScalarKind::Int128,
                    (128, false) => ScalarKind::UInt128,
                    _ => return None,
                },
                *is_const,
            ),
            _ => return None,
        };
        Some(Self { kind, is_const })
    }

    pub fn mutable_kind(value: &CppType) -> Option<ScalarKind> {
        Self::of(value)
            .filter(|scalar| !scalar.is_const)
            .map(|scalar| scalar.kind)
    }

    pub fn is(value: &CppType, kind: ScalarKind, is_const: bool) -> bool {
        Self::of(value) == Some(Self { kind, is_const })
    }

    /// The bounded native object-pointer profile. Enum values share uint8
    /// contracts, but only the authenticated standard byte declaration grants
    /// character alias access. Import validation checks its locked header pin.
    pub fn pointer_element(value: &CppType, allow_const: bool) -> Option<Self> {
        if !matches!(value, CppType::Integer { .. }) && !is_standard_byte(value) {
            return None;
        }
        Self::of(value).filter(|scalar| {
            (allow_const || !scalar.is_const)
                && matches!(
                    scalar.kind,
                    ScalarKind::Int32 | ScalarKind::UInt32 | ScalarKind::UInt8
                )
        })
    }
}

/// Nominal candidate only: the importer separately authenticates the declaration
/// span against the pinned standard header before any lowering can use it.
pub(super) fn is_standard_byte(value: &CppType) -> bool {
    matches!(value, CppType::Enumeration { declaration_id, name, is_scoped: true,
        is_fixed: true, .. } if declaration_id == "c:@N@std@E@byte" && name == "std::byte")
}

/// Direct reinterpretation is bounded to the approved declared uint32 profile
/// and genuine byte storage. Signed-int traversal needs a separate guarantee;
/// explicitly cataloged span<int> conversion is a distinct library assumption.
/// No conversion grants authority, initializes storage or creates an object.
pub(super) fn byte_pointer_cast(source: &CppType, target: &CppType) -> bool {
    matches!((source, target), (CppType::Pointer { pointee: source }, CppType::Pointer { pointee: target })
        if Scalar::pointer_element(source, false).is_some_and(|scalar|
            matches!(scalar.kind, ScalarKind::UInt32 | ScalarKind::UInt8))
            && is_standard_byte(target)
            && Scalar::pointer_element(target, false).is_some())
}

impl ScalarKind {
    pub fn is_integer(self) -> bool {
        self != Self::Bool
    }

    pub fn is_wide(self) -> bool {
        matches!(self, Self::Int128 | Self::UInt128)
    }

    pub fn kernel_type(self) -> CType {
        match self {
            Self::Bool => CType::Bool,
            Self::UInt8 => CType::UInt8,
            Self::Int32 => CType::Int32,
            Self::Int64 => CType::Int64,
            Self::UInt32 => CType::UInt32,
            Self::UInt64 => CType::UInt64,
            Self::Int128 => CType::Int128,
            Self::UInt128 => CType::UInt128,
        }
    }

    pub fn proof_type(self) -> C0Type {
        match self {
            Self::Bool => C0Type::Bool,
            Self::UInt8 => C0Type::UInt8,
            Self::Int32 => C0Type::Int32,
            Self::Int64 => C0Type::Int64(LongRank::Long),
            Self::UInt32 => C0Type::UInt32,
            Self::UInt64 => C0Type::UInt64(LongRank::Long),
            Self::Int128 => C0Type::Int128,
            Self::UInt128 => C0Type::UInt128,
        }
    }

    pub fn pointer_kernel_type(self) -> Option<CType> {
        match self {
            Self::Int32 => Some(CType::Int32Pointer),
            Self::UInt32 => Some(CType::UInt32Pointer),
            Self::UInt8 => Some(CType::UInt8Pointer),
            _ => None,
        }
    }

    pub fn pointer_proof_type(self) -> Option<C0Type> {
        match self {
            Self::Int32 => Some(C0Type::Int32Pointer),
            Self::UInt32 => Some(C0Type::UInt32Pointer),
            Self::UInt8 => Some(C0Type::UInt8Pointer),
            _ => None,
        }
    }

    pub fn parse_literal(self, value: &str) -> Option<ScalarLiteral> {
        let ty = MachineIntegerType::from_c_type(self.kernel_type())?;
        let value = MachineIntegerConstant::parse_decimal(ty.format(), value)?;
        Some(ScalarLiteral { ty, value })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ScalarLiteral {
    ty: MachineIntegerType,
    value: MachineIntegerConstant,
}

impl ScalarLiteral {
    pub fn kernel_expression(self) -> CExpression {
        CExpression::Value(
            self.ty
                .constant_value(self.value)
                .expect("a scalar literal's checked format must match its runtime type"),
        )
    }
}

/// Clang has already resolved both integer types. C++20 selects the shared
/// modulo policy explicitly; Boolean conversions retain their separate rules.
pub(super) fn convert(value: CExpression, source: ScalarKind, target: ScalarKind) -> CExpression {
    if source.is_integer() && target.is_integer() {
        kernel::c_integer_cast_modulo(value, target.kernel_type())
    } else {
        kernel::c_cast(value, target.kernel_type())
    }
}

pub(super) fn same_unqualified_integer_type(left: &CppType, right: &CppType) -> bool {
    matches!(
        (left, right),
        (
            CppType::Integer {
                bits: left_bits,
                signed: left_signed,
                ..
            },
            CppType::Integer {
                bits: right_bits,
                signed: right_signed,
                ..
            }
        ) if left_bits == right_bits && left_signed == right_signed
    )
}

/// Lvalue-to-rvalue conversion removes the object's top-level const only.
/// Pointer pointee qualification and nominal enum identity remain intact.
pub(super) fn scalar_value_type(value: &CppType) -> CppType {
    let mut value = value.clone();
    if let CppType::Integer { is_const, .. }
    | CppType::Enumeration { is_const, .. }
    | CppType::Boolean { is_const, .. } = &mut value
    {
        *is_const = false;
    }
    value
}

/// A native reference binds an object of its own type, possibly adding const
/// but never removing it.
pub(super) fn reference_binds(object: &CppType, referent: &CppType) -> bool {
    same_scalar_type(&scalar_value_type(object), &scalar_value_type(referent))
        && (Scalar::of(referent).is_some_and(|scalar| scalar.is_const)
            || !Scalar::of(object).is_some_and(|scalar| scalar.is_const))
}

/// The element a native reference refers to: an `int`, `unsigned int`,
/// `unsigned char` or `std::byte`, possibly const.
pub(super) fn reference_element(value: &CppType) -> Option<Scalar> {
    match value {
        CppType::LvalueReference { pointee } => Scalar::pointer_element(pointee, true),
        _ => None,
    }
}

/// Whether a returned reference or pointer refers to a const native element.
pub(super) fn returns_constant_element(value: &CppType) -> bool {
    match value {
        CppType::LvalueReference { pointee } | CppType::Pointer { pointee } => {
            Scalar::pointer_element(pointee, true).is_some_and(|element| element.is_const)
        }
        _ => false,
    }
}

pub(super) fn same_scalar_type(left: &CppType, right: &CppType) -> bool {
    match (left, right) {
        (CppType::Pointer { pointee: left }, CppType::Pointer { pointee: right })
        | (
            CppType::LvalueReference { pointee: left },
            CppType::LvalueReference { pointee: right },
        ) => same_scalar_type(left, right),
        (
            CppType::Integer {
                bits: left_bits,
                signed: left_signed,
                is_const: left_const,
                ..
            },
            CppType::Integer {
                bits: right_bits,
                signed: right_signed,
                is_const: right_const,
                ..
            },
        ) => left_bits == right_bits && left_signed == right_signed && left_const == right_const,
        (
            CppType::Boolean {
                bits: left_bits,
                is_const: left_const,
            },
            CppType::Boolean {
                bits: right_bits,
                is_const: right_const,
            },
        ) => left_bits == right_bits && left_const == right_const,
        _ => left == right,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_classification_preserves_qualification_and_rejects_unsupported_widths() {
        for bits in [0, 1, 8, 16, 32, 64, 128] {
            for signed in [false, true] {
                for is_const in [false, true] {
                    let ty = CppType::Integer {
                        bits,
                        signed,
                        is_const,
                        source_aliases: vec![],
                    };
                    let scalar = Scalar::of(&ty);
                    let supported = matches!(bits, 32 | 64 | 128) || (bits == 8 && !signed);
                    assert_eq!(scalar.is_some(), supported);
                    assert_eq!(Scalar::mutable_kind(&ty).is_some(), supported && !is_const);
                    if let Some(scalar) = scalar {
                        assert_eq!(scalar.is_const, is_const);
                        // Qualifiers are preserved independently of value kind.
                        let unqualified = CppType::Integer {
                            bits,
                            signed,
                            is_const: false,
                            source_aliases: vec![],
                        };
                        assert!(same_unqualified_integer_type(&ty, &unqualified));
                        assert_eq!(same_scalar_type(&ty, &unqualified), !is_const);
                        assert!(
                            Scalar::of(&CppType::Pointer {
                                pointee: Box::new(ty)
                            })
                            .is_none()
                        );
                    }
                }
            }
        }
        for bits in [1, 8, 32] {
            assert_eq!(
                Scalar::mutable_kind(&CppType::Boolean {
                    bits,
                    is_const: false
                }),
                (bits == 8).then_some(ScalarKind::Bool)
            );
        }
    }

    #[test]
    fn integer_literals_use_one_checked_interpretation_at_both_boundaries() {
        for (kind, accepted, rejected) in [
            (
                ScalarKind::UInt8,
                vec!["0", "128", "255"],
                vec!["-1", "256"],
            ),
            (
                ScalarKind::Int32,
                vec!["-2147483648", "2147483647", "0"],
                vec!["-2147483649", "2147483648"],
            ),
            (
                ScalarKind::Int64,
                vec!["-9223372036854775808", "9223372036854775807", "0"],
                vec!["-9223372036854775809", "9223372036854775808"],
            ),
            (
                ScalarKind::Int128,
                vec![
                    "-170141183460469231731687303715884105728",
                    "170141183460469231731687303715884105727",
                    "0",
                ],
                vec![
                    "-170141183460469231731687303715884105729",
                    "170141183460469231731687303715884105728",
                ],
            ),
            (
                ScalarKind::UInt128,
                vec![
                    "0",
                    "18446744073709551616",
                    "340282366920938463463374607431768211455",
                ],
                vec!["-1", "340282366920938463463374607431768211456"],
            ),
            (
                ScalarKind::UInt32,
                vec!["0", "4294967295"],
                vec!["-1", "4294967296"],
            ),
            (
                ScalarKind::UInt64,
                vec!["0", "18446744073709551615"],
                vec!["-1", "18446744073709551616"],
            ),
        ] {
            for value in accepted {
                let parsed = kind.parse_literal(value).unwrap();
                // All parsed boundary values produce a typed kernel literal.
                let _ = parsed.kernel_expression();
            }
            for value in rejected.into_iter().chain(["", "1.0", "not-an-integer"]) {
                assert!(kind.parse_literal(value).is_none(), "{kind:?}: {value}");
            }
        }
        assert!(ScalarKind::Bool.parse_literal("1").is_none());
    }

    #[test]
    fn cpp20_constant_conversions_use_modulo_policy_and_preserve_target_type() {
        for (source, literal, target, expected) in [
            (
                ScalarKind::UInt64,
                "18446744073709551615",
                ScalarKind::Int64,
                "-1",
            ),
            (
                ScalarKind::Int64,
                "-9223372036854775808",
                ScalarKind::Int32,
                "0",
            ),
            (
                ScalarKind::Int64,
                "9223372036854775807",
                ScalarKind::Int32,
                "-1",
            ),
            (
                ScalarKind::Int32,
                "-1",
                ScalarKind::UInt64,
                "18446744073709551615",
            ),
            (
                ScalarKind::UInt32,
                "4294967295",
                ScalarKind::Int64,
                "4294967295",
            ),
            (ScalarKind::Int64, "-1", ScalarKind::UInt32, "4294967295"),
            (ScalarKind::UInt32, "4294967295", ScalarKind::Int32, "-1"),
        ] {
            let converted = convert(
                source.parse_literal(literal).unwrap().kernel_expression(),
                source,
                target,
            );
            let actual =
                kernel::prove_c_expression_evaluation(kernel::CState::new(), converted).unwrap();
            let expected = kernel::prove_c_expression_evaluation(
                kernel::CState::new(),
                target.parse_literal(expected).unwrap().kernel_expression(),
            )
            .unwrap();
            let outcome = |theorem: &kernel::Theorem| {
                let kernel::Proposition::CExpressionEvaluates { outcome, .. } =
                    theorem.proposition()
                else {
                    panic!("expected expression evaluation");
                };
                outcome.clone()
            };
            assert_eq!(outcome(&actual), outcome(&expected));
        }
        // Nonconstant casts retain the checked runtime operation and its
        // language-specific policy; constant folding does not erase operands.
        let variable = crate::kernel::c_variable("wide");
        assert_eq!(
            convert(variable.clone(), ScalarKind::UInt64, ScalarKind::Int64),
            kernel::c_integer_cast_modulo(variable, CType::Int64)
        );
    }
}
