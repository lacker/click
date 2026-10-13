//! Bounded source spellings. Exact rendering refuses unknown operands;
//! diagnostic-only partial rendering labels them with explicit placeholders.
use super::*;

#[cfg(test)]
pub(super) fn render(proposition: &Proposition, labels: &SnapshotLabels) -> Option<String> {
    Printer {
        labels,
        remaining: 512,
        unnamed: None,
        explicit_identity: false,
    }
    .proposition(proposition, 0)
    .filter(|text| text.len() <= 2048)
}

/// Readable display only when it preserves every checked operand identity.
/// Source citation recovery is separate: an unqualified source read may be a
/// valid citation at one point without identifying its snapshot in a report.
pub(super) fn display(proposition: &Proposition, labels: &SnapshotLabels) -> Option<String> {
    Printer {
        labels,
        remaining: 512,
        unnamed: None,
        explicit_identity: true,
    }
    .proposition(proposition, 0)
    .filter(|text| text.len() <= 2048)
}

pub(super) fn integer(value: &IntegerTerm, labels: &SnapshotLabels) -> Option<String> {
    Printer {
        labels,
        remaining: 512,
        unnamed: None,
        explicit_identity: false,
    }
    .integer(value, 0)
    .filter(|text| text.len() <= 2048)
}

struct Printer<'a> {
    labels: &'a SnapshotLabels,
    explicit_identity: bool,
    remaining: usize,
    unnamed: Option<&'a mut HashMap<Variable, String>>,
}

/// A presentation-only partial spelling. Exact citation rendering above
/// still refuses unnamed operands. Share report-local placeholder identities.
#[cfg(test)]
pub(super) fn partial(proposition: &Proposition, labels: &mut SnapshotLabels) -> Option<String> {
    let mut unnamed = std::mem::take(&mut labels.anonymous_names);
    let text = Printer {
        labels,
        remaining: 512,
        unnamed: Some(&mut unnamed),
        explicit_identity: false,
    }
    .proposition(proposition, 0)
    .filter(|text| text.len() <= 2048);
    labels.anonymous_names = unnamed;
    text
}

impl Printer<'_> {
    fn unnamed_variable(&mut self, variable: Variable) -> Option<String> {
        let names = self.unnamed.as_deref_mut()?;
        let next = names.len();
        let name = names
            .entry(variable)
            .or_insert_with(|| format!("value {}", alphabetic_label(next)));
        Some(format!(
            "<unnamed {}>",
            name.strip_prefix("value ").unwrap_or(name)
        ))
    }

    fn visit(&mut self, depth: usize) -> Option<()> {
        if depth >= 32 || self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        Some(())
    }

    fn proposition(&mut self, proposition: &Proposition, depth: usize) -> Option<String> {
        self.visit(depth)?;
        let depth = depth + 1;
        match proposition {
            Proposition::ConditionIs(condition, polarity) => {
                self.condition(condition, *polarity, depth)
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                let op = match proposition {
                    Proposition::And(..) => "and",
                    Proposition::Or(..) => "or",
                    _ => "implies",
                };
                Some(format!(
                    "({}) {op} ({})",
                    self.proposition(left, depth)?,
                    self.proposition(right, depth)?
                ))
            }
            Proposition::Not(body) => Some(format!("not ({})", self.proposition(body, depth)?)),
            Proposition::Equal(left, right) => Some(format!(
                "{} == {}",
                self.term(left, depth)?,
                self.term(right, depth)?
            )),
            _ => None,
        }
    }

    fn condition(
        &mut self,
        condition: &ConditionTerm,
        polarity: bool,
        depth: usize,
    ) -> Option<String> {
        self.visit(depth)?;
        let depth = depth + 1;
        let (left, right, positive, negative) = match condition {
            ConditionTerm::Constant(value) => return Some((value == &polarity).to_string()),
            ConditionTerm::PointerEqual(left, right) => {
                if self.explicit_identity
                    && [left, right]
                        .iter()
                        .any(|p| crate::surface::proof_trace::pointer_definition(p).is_some())
                {
                    return None;
                }
                // Without retained pointee types, do not claim two different
                // named pointers form a well-typed source comparison.
                if left != right && **left != Pointer::null() && **right != Pointer::null() {
                    return None;
                }
                let pointer = |p: &Pointer| {
                    if p == &Pointer::null() {
                        Some("0".to_owned())
                    } else {
                        self.labels.pointer_sources.get(p).cloned()
                    }
                };
                return Some(format!(
                    "{} {} {}",
                    pointer(left)?,
                    if polarity { "==" } else { "!=" },
                    pointer(right)?
                ));
            }
            ConditionTerm::AlgebraicEqual(left, right) => {
                return Some(format!(
                    "{} {} {}",
                    self.algebraic(left, depth)?,
                    if polarity { "==" } else { "!=" },
                    self.algebraic(right, depth)?
                ));
            }
            ConditionTerm::Bitvector32Equal(a, b) | ConditionTerm::Bitvector64Equal(a, b) => {
                (a, b, "==", "!=")
            }
            ConditionTerm::Bitvector32SignedLessThan(a, b)
            | ConditionTerm::Bitvector64SignedLessThan(a, b) => (a, b, "<", ">="),
            ConditionTerm::Bitvector32SignedLessEqual(a, b)
            | ConditionTerm::Bitvector64SignedLessEqual(a, b) => (a, b, "<=", ">"),
            ConditionTerm::Bitvector32SignedGreaterThan(a, b)
            | ConditionTerm::Bitvector64SignedGreaterThan(a, b) => (a, b, ">", "<="),
            ConditionTerm::Bitvector32SignedGreaterEqual(a, b)
            | ConditionTerm::Bitvector64SignedGreaterEqual(a, b) => (a, b, ">=", "<"),
            // A `uint64` comparison is written with the same operators; its
            // operands' type is what makes it unsigned.
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => (a, b, "<", ">="),
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => (a, b, "<=", ">"),
            ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => (a, b, ">", "<="),
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => (a, b, ">=", "<"),
            ConditionTerm::Bitvector32SignedAddOverflows(a, b)
            | ConditionTerm::Bitvector32SignedSubtractOverflows(a, b) => {
                let Bitvector32Term::Constant(bits) = b.as_ref() else {
                    return None;
                };
                let offset = *bits as i32 as i64;
                if offset == 0 {
                    return Some((!polarity).to_string());
                }
                let addition =
                    matches!(condition, ConditionTerm::Bitvector32SignedAddOverflows(..));
                let lower = if addition { offset < 0 } else { offset > 0 };
                let bound = if addition {
                    if lower {
                        i32::MIN as i64 - offset
                    } else {
                        i32::MAX as i64 - offset
                    }
                } else if lower {
                    i32::MIN as i64 + offset
                } else {
                    i32::MAX as i64 + offset
                };
                let op = match (lower, polarity) {
                    (true, true) => "<",
                    (true, false) => ">=",
                    (false, true) => ">",
                    (false, false) => "<=",
                };
                return Some(format!("{} {op} {bound}", self.bitvector(a, depth)?));
            }
            crate::kernel::integer_comparison_condition!(a, b) => {
                let (positive, negative) = match condition {
                    ConditionTerm::IntegerEqual(..) => ("==", "!="),
                    ConditionTerm::IntegerNotEqual(..) => ("!=", "=="),
                    ConditionTerm::IntegerLessThan(..) => ("<", ">="),
                    ConditionTerm::IntegerLessEqual(..) => ("<=", ">"),
                    ConditionTerm::IntegerGreaterThan(..) => (">", "<="),
                    _ => (">=", "<"),
                };
                return Some(format!(
                    "{} {} {}",
                    self.integer(a, depth)?,
                    if polarity { positive } else { negative },
                    self.integer(b, depth)?
                ));
            }
            _ => return None,
        };
        let operator = if polarity { positive } else { negative };
        // Lowered unsigned 32-bit order flips both sign bits. Recover the
        // comparison, keeping the unsigned interpretation visible.
        const SIGN: u32 = 0x8000_0000;
        fn flipped(value: &Bitvector32Term) -> Option<&Bitvector32Term> {
            const SIGN: u32 = 0x8000_0000;
            match value {
                Bitvector32Term::BitwiseXor(a, b) if b.as_const() == Some(SIGN) => Some(a.as_ref()),
                Bitvector32Term::BitwiseXor(a, b) if a.as_const() == Some(SIGN) => Some(b.as_ref()),
                _ => None,
            }
        }
        if !matches!(condition, ConditionTerm::Bitvector32Equal(..))
            && (flipped(left).is_some() || flipped(right).is_some())
        {
            let recover = |value: &Bitvector32Term| {
                flipped(value).cloned().or_else(|| {
                    value
                        .as_const()
                        .map(|v| Bitvector32Term::Constant(v ^ SIGN))
                })
            };
            return Some(format!(
                "{} {operator} {} (unsigned)",
                self.comparison_operand(&recover(left)?, Some(false), depth)?,
                self.comparison_operand(&recover(right)?, Some(false), depth)?
            ));
        }
        let signed = if matches!(condition, ConditionTerm::Bitvector32Equal(..)) {
            [left.as_ref(), right.as_ref()].iter().find_map(|term| {
                let Bitvector32Term::Variable(variable) = term else {
                    return None;
                };
                match self.labels.source_types.get(variable) {
                    Some(crate::kernel::CType::Int32) => Some(true),
                    Some(crate::kernel::CType::UInt32) => Some(false),
                    _ => None,
                }
            })
        } else {
            Some(true)
        };
        Some(format!(
            "{} {operator} {}",
            self.comparison_operand(left, signed, depth)?,
            self.comparison_operand(right, signed, depth)?
        ))
    }

    fn comparison_operand(
        &mut self,
        value: &Bitvector32Term,
        signed: Option<bool>,
        depth: usize,
    ) -> Option<String> {
        if signed == Some(true) && matches!(value, Bitvector32Term::UInt32From64(_)) {
            return Some({
                let value = self.bitvector(value, depth)?;
                if crate::surface::diagnostics::rust_spelling() {
                    format!("({value} as i32)")
                } else {
                    format!("(int32)({value})")
                }
            });
        }
        if let Bitvector32Term::Constant(value) = value {
            return match signed {
                Some(true) => Some((*value as i32).to_string()),
                Some(false) => Some(value.to_string()),
                None if *value <= i32::MAX as u32 => Some(value.to_string()),
                None => None,
            };
        }
        self.bitvector(value, depth)
    }

    fn term(&mut self, term: &Term, depth: usize) -> Option<String> {
        self.visit(depth)?;
        match term {
            Term::Bitvector32(value) => self.bitvector(value, depth + 1),
            Term::Integer(value) => self.integer(value, depth + 1),
            Term::Condition(ConditionTerm::Constant(value)) => Some(value.to_string()),
            Term::CValue(value) => self.cvalue(value, depth + 1),
            Term::Algebraic(value) => self.algebraic(value, depth + 1),
            _ => None,
        }
    }

    fn bitvector(&mut self, value: &Bitvector32Term, depth: usize) -> Option<String> {
        self.visit(depth)?;
        let depth = depth + 1;
        match value {
            Bitvector32Term::Constant(value) if *value <= i32::MAX as u32 => {
                Some(value.to_string())
            }
            Bitvector32Term::Int64Constant(value) => Some(format!("{value}i64")),
            Bitvector32Term::UInt64Constant(value) => Some(format!("{value}u64")),
            Bitvector32Term::Variable(variable) => {
                if self.explicit_identity && crate::kernel::is_load_variable(variable) {
                    return None;
                }
                if let Some(name) = self.labels.source_name_for(*variable) {
                    return Some(name.to_owned());
                }
                if let Some((memory, pointer)) =
                    crate::kernel::registered_load_for_variable(variable)
                {
                    return self.load(
                        memory.memory(),
                        &pointer,
                        crate::kernel::registered_load_kind_for_variable(variable)?,
                    );
                }
                crate::kernel::model_fields::model_field_spelling(*variable)
                    .or_else(|| self.unnamed_variable(*variable))
            }
            Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
                self.load(memory.as_ref(), pointer, *kind)
            }
            Bitvector32Term::Add(a, b)
            | Bitvector32Term::Subtract(a, b)
            | Bitvector32Term::Multiply(a, b)
            | Bitvector32Term::UInt64Add(a, b)
            | Bitvector32Term::UInt64Subtract(a, b)
            | Bitvector32Term::UInt64Multiply(a, b)
            | Bitvector32Term::UInt64Divide(a, b)
            | Bitvector32Term::UInt64Remainder(a, b) => {
                let op = match value {
                    Bitvector32Term::Add(..) | Bitvector32Term::UInt64Add(..) => "+",
                    Bitvector32Term::Subtract(..) | Bitvector32Term::UInt64Subtract(..) => "-",
                    Bitvector32Term::UInt64Divide(..) => "/",
                    Bitvector32Term::UInt64Remainder(..) => "%",
                    _ => "*",
                };
                Some(format!(
                    "({} {op} {})",
                    self.bitvector(a, depth)?,
                    self.bitvector(b, depth)?
                ))
            }
            Bitvector32Term::UInt32From64(value) => Some({
                let value = self.bitvector(value, depth)?;
                if crate::surface::diagnostics::rust_spelling() {
                    format!("({value} as u32)")
                } else {
                    format!("(uint32)({value})")
                }
            }),
            _ => None,
        }
    }

    fn load(
        &self,
        memory: &CMemory,
        pointer: &Pointer,
        kind: crate::kernel::LoadKind,
    ) -> Option<String> {
        if self.explicit_identity {
            return None;
        }
        let (point, naming) = self.labels.source_memory_context(memory)?;
        if point.len() > 256 {
            return None;
        }
        // An address spelling alone does not establish the type of a read.
        // Keep only bases whose declared element has this exact load kind.
        let (names, values): (Vec<_>, Vec<_>) = naming
            .0
            .iter()
            .zip(&naming.1)
            .filter(|(name, _)| name.name().len() <= 256)
            .filter(|(_, value)| match value {
                crate::kernel::CExpression::Value(crate::kernel::CValue::Pointer(base)) => {
                    base.c_type()
                        .pointee_type()
                        .and_then(crate::kernel::LoadKind::of_type)
                        == Some(kind)
                }
                _ => true,
            })
            .map(|(name, value)| (name.clone(), value.clone()))
            .unzip();
        let cell = crate::surface::diagnostics::diagnostic_source_load_cell(
            pointer,
            kind,
            ParameterBinding::new(&names, &values),
        )?;
        Some(if point == "current" {
            cell
        } else {
            format!("at({point}, {cell})")
        })
    }

    fn cvalue(&mut self, value: &crate::kernel::CValue, depth: usize) -> Option<String> {
        self.visit(depth)?;
        use crate::kernel::CValue;
        match value {
            CValue::Bool(Bitvector32Term::Constant(0)) => Some("false".into()),
            CValue::Bool(Bitvector32Term::Constant(1)) => Some("true".into()),
            CValue::Bool(value) | CValue::Int64(value) | CValue::UInt64(value) => {
                self.bitvector(value, depth + 1)
            }
            CValue::PointerInteger(value) => self.cvalue(&value.numeric_value(), depth + 1),
            CValue::Int32(value) => self.comparison_operand(value, Some(true), depth + 1),
            CValue::UInt32(value) => self.comparison_operand(value, Some(false), depth + 1),
            CValue::Pointer(pointer) => {
                self.pointer_value_name(pointer, self.labels.naming.as_ref()?)
            }
            _ => None,
        }
    }

    fn pointer_value_name(
        &self,
        pointer: &crate::kernel::CPointerValue,
        naming: &NamingTables,
    ) -> Option<String> {
        if self.explicit_identity
            && crate::surface::proof_trace::pointer_definition(pointer.pointer()).is_some()
        {
            return None;
        }
        naming
            .0
            .iter()
            .zip(&naming.1)
            .find_map(|(name, value)| match value {
                crate::kernel::CExpression::Value(crate::kernel::CValue::Pointer(base))
                    if base == pointer
                        && base.c_type() == pointer.c_type()
                        && name.name().len() <= 256 =>
                {
                    Some(name.name().to_owned())
                }
                _ => None,
            })
    }

    fn pure_argument(&mut self, argument: &PureFunctionArgument, depth: usize) -> Option<String> {
        self.visit(depth)?;
        match argument {
            PureFunctionArgument::Value(value) => self.cvalue(value, depth + 1),
            PureFunctionArgument::Integer(value) => self.integer(value, depth + 1),
            PureFunctionArgument::Algebraic(value) => self.algebraic(value, depth + 1),
            PureFunctionArgument::ArrayRef {
                memory,
                pointer: crate::kernel::CValue::Pointer(pointer),
                element_type,
            } => {
                if pointer.c_type().pointee_type() != Some(*element_type) {
                    return None;
                }
                if self.explicit_identity {
                    return None;
                }
                let (point, naming) = self.labels.source_memory_context(memory)?;
                let name = self.pointer_value_name(pointer, naming)?;
                Some(if point == "current" {
                    name
                } else {
                    format!("at({point}, {name})")
                })
            }
            _ => None,
        }
    }

    fn call(
        &mut self,
        name: &str,
        arguments: &[PureFunctionArgument],
        depth: usize,
    ) -> Option<String> {
        self.visit(depth)?;
        if name.len() > 256 {
            return None;
        }
        let arguments = arguments
            .iter()
            .map(|argument| self.pure_argument(argument, depth + 1))
            .collect::<Option<Vec<_>>>()?;
        let text = format!("{name}({})", arguments.join(", "));
        (text.len() <= 2048).then_some(text)
    }

    fn algebraic(&mut self, value: &AlgebraicTerm, depth: usize) -> Option<String> {
        self.visit(depth)?;
        match &value.node {
            AlgebraicTermNode::Variable(variable) => self
                .labels
                .source_name_for(*variable)
                .map(str::to_owned)
                .or_else(|| self.unnamed_variable(*variable)),
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                self.call(name, arguments, depth + 1)
            }
            AlgebraicTermNode::Constructor { variant, fields } => {
                if value.algebraic_type.name.len() + variant.len() > 256 {
                    return None;
                }
                let fields = fields
                    .iter()
                    .map(|field| match field {
                        AlgebraicValue::C(value) => self.cvalue(value, depth + 1),
                        AlgebraicValue::Integer(value) => self.integer(value, depth + 1),
                        AlgebraicValue::Algebraic(value) => self.algebraic(value, depth + 1),
                    })
                    .collect::<Option<Vec<_>>>()?;
                let name = format!("{}::{variant}", value.algebraic_type.name);
                Some(if fields.is_empty() {
                    name
                } else {
                    format!("{name}({})", fields.join(", "))
                })
            }
            _ => None,
        }
    }

    fn integer(&mut self, value: &IntegerTerm, depth: usize) -> Option<String> {
        self.visit(depth)?;
        let depth = depth + 1;
        match value {
            IntegerTerm::Constant(value) if value.bits() <= 256 => Some(value.to_string()),
            IntegerTerm::Variable(variable) => self
                .labels
                .source_name_for(*variable)
                .map(str::to_owned)
                .or_else(|| crate::kernel::model_fields::model_field_spelling(*variable))
                .or_else(|| self.unnamed_variable(*variable)),
            IntegerTerm::PureFunctionApplication(application) => {
                self.call(application.name(), application.arguments(), depth)
            }
            IntegerTerm::Negate(value) => Some(format!("(-{})", self.integer(value, depth)?)),
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) | IntegerTerm::Multiply(a, b) => {
                let op = match value {
                    IntegerTerm::Add(..) => "+",
                    IntegerTerm::Subtract(..) => "-",
                    _ => "*",
                };
                Some(format!(
                    "({} {op} {})",
                    self.integer(a, depth)?,
                    self.integer(b, depth)?
                ))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{CPointerValue, CType, CValue, LoadKind, PointerBlock, SharedCMemory};

    fn equality(value: Bitvector32Term) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        )
    }

    #[test]
    fn named_pure_function_facts_keep_their_surface_arguments() {
        let mut labels = SnapshotLabels::default();
        labels.source_name(Variable(7), "r".into());
        let application = crate::kernel::SharedPureApplication::intern(
            "size".into(),
            vec![PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(Variable(7)),
            ))],
        );
        let fact = Proposition::Equal(
            Term::Integer(IntegerTerm::PureFunctionApplication(application)),
            Term::Integer(IntegerTerm::from(3)),
        );
        assert_eq!(render(&fact, &labels), Some("size(r) == 3".into()));
    }

    #[test]
    fn unnamed_operands_keep_their_context_without_becoming_exact_citations() {
        let mut labels = SnapshotLabels::default();
        for depth in [0, 16, 64, 256] {
            let mut term = Bitvector32Term::Variable(Variable(999));
            for _ in 0..depth {
                term = Bitvector32Term::Add(Box::new(term), Box::new(Bitvector32Term::Constant(1)));
            }
            let fact = equality(term);
            assert!(render(&fact, &labels).is_none());
            let text = super::super::render_proposition_labeled(&fact, &mut labels);
            if depth < 96 {
                assert!(text.contains("value A"), "{text}");
            } else {
                assert!(text.contains("<proof proposition truncated>"), "{text}");
            }
            assert!(!text.contains("no exact Click spelling"), "{text}");
            assert!(text.len() < 32 * 1024);
        }
    }

    #[test]
    fn partial_facts_share_placeholder_identities_within_one_report() {
        let mut labels = SnapshotLabels::default();
        let first = equality(Bitvector32Term::Variable(Variable(998)));
        let second = equality(Bitvector32Term::Variable(Variable(999)));
        assert_eq!(partial(&first, &mut labels).unwrap(), "<unnamed A> == 0");
        assert_eq!(partial(&second, &mut labels).unwrap(), "<unnamed B> == 0");
        assert_eq!(partial(&first, &mut labels).unwrap(), "<unnamed A> == 0");
        assert!(render(&first, &labels).is_none());
    }

    #[test]
    fn narrowed_wide_values_keep_the_signed_comparison_view() {
        let state = CState::new().with_local(
            "size",
            CValue::UInt64(Bitvector32Term::Variable(Variable(94))),
        );
        let labels = SnapshotLabels::with_state(ParameterBinding::default(), &state);
        let value =
            Bitvector32Term::UInt32From64(Box::new(Bitvector32Term::Variable(Variable(94))));
        let fact = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(value),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        assert_eq!(
            render(&fact, &labels).unwrap(),
            "(int32)((uint32)(size)) < 0"
        );
    }

    #[test]
    fn historical_loads_use_their_own_state_names_and_keep_their_read_type() {
        let pointer = Pointer {
            block: PointerBlock::Concrete("global:cells".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let base = CValue::Pointer(CPointerValue::new(pointer.clone(), CType::Int32Pointer));
        let before = CState::new()
            .with_local("cells", base.clone())
            .with_memory(CMemory::new().with_block("global:cells", 4));
        let after = before
            .clone()
            .with_memory(CMemory::new().with_block("global:cells", 8));
        let mut labels = SnapshotLabels::with_state(ParameterBinding::default(), &after);
        labels.source_state(&before, "pre".into());
        let load = |memory: &CMemory, kind| {
            equality(Bitvector32Term::MemoryLoad(
                SharedCMemory::from(memory.clone()),
                Box::new(pointer.clone()),
                kind,
            ))
        };
        assert_eq!(
            render(&load(before.memory(), LoadKind::Bits32), &labels),
            Some("at(pre, cells[0]) == 0".into())
        );
        assert_eq!(
            render(&load(after.memory(), LoadKind::Bits32), &labels),
            Some("cells[0] == 0".into())
        );
        assert_eq!(
            render(&load(before.memory(), LoadKind::UInt8), &labels),
            None
        );
        let unknown = CMemory::new().with_block("global:cells", 16);
        assert_eq!(render(&load(&unknown, LoadKind::Bits32), &labels), None);
    }

    #[test]
    fn reassigned_parameters_do_not_rename_their_old_value_as_current() {
        let entry =
            CState::new().with_local("i", CValue::Int32(Bitvector32Term::Variable(Variable(7))));
        let current = entry
            .clone()
            .with_local("i", CValue::Int32(Bitvector32Term::Variable(Variable(8))));
        let (names, values) = crate::surface::diagnostics::local_naming_tables(&entry);
        let labels = SnapshotLabels::with_state(ParameterBinding::new(&names, &values), &current);
        assert_eq!(
            render(&equality(Bitvector32Term::Variable(Variable(7))), &labels),
            Some("at(function.entry, i) == 0".into())
        );
        assert_eq!(
            render(&equality(Bitvector32Term::Variable(Variable(8))), &labels),
            Some("i == 0".into())
        );
    }
}
