//! Click and source spellings of checked kernel terms.
//!
//! One printer serves two policies. Ordinary diagnostics use the *source*
//! policy, which is total: every fact, goal and value is spelled in Click or
//! C syntax with minimal parentheses, and the parts with no source name get
//! an explicit placeholder (`<unnamed A>`, `<pointer A>`, `at(<state A>, x)`)
//! rather than a kernel identity. The *exact* policies refuse (return
//! `None`) whenever an operand has no source spelling, so a proof trace can
//! fall back to its typed notation.
//!
//! A read keeps the memory it reads: a read of the state being reported is
//! the bare place (`a[i]`), a read of the function's entry memory is
//! `old(a[i])`, a read of a recorded program point is `at(point, a[i])`, and a
//! read of any other memory is `at(<state A>, a[i])`, with `<state A>` defined
//! after the report. Two reads of one place in two memories therefore never
//! print alike.
use super::*;

/// Which spelling policy a printer applies.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    /// Total source spelling for ordinary diagnostics.
    Source,
    /// Exact Click spelling, refusing unnamed operands.
    #[cfg_attr(not(test), allow(dead_code))]
    Exact,
    /// Exact spelling that also refuses every read, whose snapshot an
    /// unqualified source spelling would hide.
    ExactIdentity,
}

/// A spelled expression and the precedence of its outermost operator.
struct Spelled {
    text: String,
    precedence: u8,
}

// Contract-expression precedence, from `docs/reference/language/grammar.md`.
const ATOM: u8 = 30;
const UNARY: u8 = 20;
const MULTIPLY: u8 = 14;
const ADD: u8 = 13;
const SHIFT: u8 = 12;
const BITWISE_AND: u8 = 11;
const BITWISE_XOR: u8 = 10;
const BITWISE_OR: u8 = 9;
// Proposition precedence. A comparison is an atom among propositions.
const NOT: u8 = 4;
const AND: u8 = 3;
const OR: u8 = 2;
const IMPLIES: u8 = 1;

fn atom(text: impl Into<String>) -> Spelled {
    Spelled {
        text: text.into(),
        precedence: ATOM,
    }
}

fn spelled(text: String, precedence: u8) -> Spelled {
    Spelled { text, precedence }
}

/// `value` as an operand that needs at least `minimum` precedence.
fn operand(value: Spelled, minimum: u8) -> String {
    if value.precedence >= minimum {
        value.text
    } else {
        format!("({})", value.text)
    }
}

/// The source type a value is read as, where the printer can tell. It
/// decides how a constant beside it is written: `-56` for an `int32`,
/// `4294967240u32` for a `uint32`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Hint {
    Signed32,
    Unsigned32,
    Narrow { signed: bool },
    Int64,
    UInt64,
}

impl Hint {
    fn of_type(c_type: crate::kernel::CType) -> Option<Self> {
        use crate::kernel::CType;
        Some(match c_type {
            CType::Int32 => Self::Signed32,
            CType::UInt32 => Self::Unsigned32,
            CType::Int8 | CType::Int16 => Self::Narrow { signed: true },
            CType::Bool | CType::UInt8 | CType::UInt16 => Self::Narrow { signed: false },
            CType::Int64 => Self::Int64,
            CType::UInt64 => Self::UInt64,
            _ => return None,
        })
    }

    fn of_load(kind: crate::kernel::LoadKind) -> Option<Self> {
        use crate::kernel::LoadKind;
        match kind {
            LoadKind::Int8 | LoadKind::Int16 => Some(Self::Narrow { signed: true }),
            LoadKind::UInt8 | LoadKind::UInt16 => Some(Self::Narrow { signed: false }),
            _ => None,
        }
    }

    fn of_machine(ty: crate::kernel::MachineIntegerType) -> Option<Self> {
        use crate::kernel::MachineIntegerType as M;
        Some(match ty {
            M::Int32 => Self::Signed32,
            M::UInt32 => Self::Unsigned32,
            M::Int8 | M::Int16 => Self::Narrow { signed: true },
            M::UInt8 | M::UInt16 => Self::Narrow { signed: false },
            M::Int64 => Self::Int64,
            M::UInt64 => Self::UInt64,
            M::Int128 | M::UInt128 => return None,
        })
    }
}

fn machine_type_spelling(ty: crate::kernel::MachineIntegerType) -> &'static str {
    use crate::kernel::MachineIntegerType as M;
    match ty {
        M::Int8 => "int8",
        M::Int16 => "int16",
        M::Int32 => "int32",
        M::UInt8 => "uint8",
        M::UInt16 => "uint16",
        M::UInt32 => "uint32",
        M::Int64 => "int64",
        M::UInt64 => "uint64",
        M::Int128 => "int128",
        M::UInt128 => "uint128",
    }
}

fn cast(type_name: &str, value: Spelled) -> Spelled {
    if crate::surface::diagnostics::rust_spelling() {
        let rust_name = match type_name {
            "int8" => "i8",
            "int16" => "i16",
            "int32" => "i32",
            "int64" => "i64",
            "uint8" => "u8",
            "uint16" => "u16",
            "uint32" => "u32",
            "uint64" => "u64",
            other => other,
        };
        return atom(format!("({} as {rust_name})", value.text));
    }
    spelled(format!("({type_name}){}", operand(value, UNARY)), UNARY)
}

pub(super) fn display(proposition: &Proposition, labels: &mut SnapshotLabels) -> Option<String> {
    printer(labels, Mode::ExactIdentity)
        .proposition(proposition, 0)
        .map(|value| value.text)
        .filter(|text| text.len() <= 2048)
}

/// The total source spelling of one proposition.
pub(super) fn source(proposition: &Proposition, labels: &mut SnapshotLabels) -> String {
    bounded(
        printer(labels, Mode::Source)
            .proposition(proposition, 0)
            .map_or_else(|| "…".into(), |value| value.text),
    )
}

/// The total source spelling of one C value.
pub(super) fn source_value(value: &crate::kernel::CValue, labels: &mut SnapshotLabels) -> String {
    bounded(
        printer(labels, Mode::Source)
            .cvalue(value, 0)
            .map_or_else(|| "…".into(), |value| value.text),
    )
}

/// The total source spelling of one exact-arithmetic term.
pub(super) fn integer(value: &IntegerTerm, labels: &mut SnapshotLabels) -> String {
    bounded(
        printer(labels, Mode::Source)
            .integer(value, 0)
            .map_or_else(|| "…".into(), |value| value.text),
    )
}

#[cfg(test)]
pub(super) fn render(proposition: &Proposition, labels: &mut SnapshotLabels) -> Option<String> {
    printer(labels, Mode::Exact)
        .proposition(proposition, 0)
        .map(|value| value.text)
        .filter(|text| text.len() <= 2048)
}

const MAX_TEXT: usize = 4096;

fn bounded(mut text: String) -> String {
    if text.len() > MAX_TEXT {
        let mut end = MAX_TEXT;
        while !text.is_char_boundary(end) {
            end -= 1;
        }
        text.truncate(end);
        text.push('…');
    }
    text
}

fn printer(labels: &mut SnapshotLabels, mode: Mode) -> Printer<'_> {
    Printer {
        labels,
        mode,
        remaining: 512,
        bound: Vec::new(),
    }
}

struct Printer<'a> {
    labels: &'a mut SnapshotLabels,
    mode: Mode,
    remaining: usize,
    /// Names of the binders in scope, innermost last.
    bound: Vec<(Variable, String)>,
}

impl Printer<'_> {
    fn source_mode(&self) -> bool {
        self.mode == Mode::Source
    }

    /// A placeholder in source mode; a refusal in the exact modes.
    fn placeholder(&mut self, text: impl FnOnce(&mut Self) -> String) -> Option<Spelled> {
        if self.source_mode() {
            Some(atom(text(self)))
        } else {
            None
        }
    }

    /// Past the node budget, source mode elides the rest of the term.
    fn enter(&mut self, depth: usize) -> Result<(), Option<Spelled>> {
        if depth < 32 && self.remaining > 0 {
            self.remaining -= 1;
            Ok(())
        } else if self.source_mode() {
            Err(Some(atom("…")))
        } else {
            Err(None)
        }
    }

    fn unnamed_variable(&mut self, variable: Variable) -> String {
        let names = &mut self.labels.anonymous_names;
        let next = names.len();
        let name = names
            .entry(variable)
            .or_insert_with(|| format!("value {}", alphabetic_label(next)));
        format!("<unnamed {}>", name.strip_prefix("value ").unwrap_or(name))
    }

    fn variable_name(&self, variable: Variable) -> Option<String> {
        self.bound
            .iter()
            .rev()
            .find(|(bound, _)| *bound == variable)
            .map(|(_, name)| name.clone())
            .or_else(|| self.labels.source_name_for(variable).map(str::to_owned))
    }

    fn binder(&mut self, variable: Variable) -> String {
        let name = if self.bound.is_empty() {
            "k".to_string()
        } else {
            format!("k{}", self.bound.len())
        };
        self.bound.push((variable, name.clone()));
        name
    }

    fn proposition(&mut self, proposition: &Proposition, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        match proposition {
            Proposition::ConditionIs(condition, polarity) => {
                self.condition(condition, *polarity, depth)
            }
            Proposition::And(left, right) => {
                let left = self.proposition(left, depth)?;
                let right = self.proposition(right, depth)?;
                Some(spelled(
                    format!("{} and {}", operand(left, AND), operand(right, AND + 1)),
                    AND,
                ))
            }
            Proposition::Or(left, right) => {
                let left = self.proposition(left, depth)?;
                let right = self.proposition(right, depth)?;
                Some(spelled(
                    format!("{} or {}", operand(left, OR), operand(right, OR + 1)),
                    OR,
                ))
            }
            Proposition::Implies(left, right) => {
                let left = self.proposition(left, depth)?;
                let right = self.proposition(right, depth)?;
                Some(spelled(
                    format!(
                        "{} implies {}",
                        operand(left, IMPLIES + 1),
                        operand(right, IMPLIES)
                    ),
                    IMPLIES,
                ))
            }
            Proposition::Not(body) => {
                let body = self.proposition(body, depth)?;
                Some(negation(body))
            }
            Proposition::Equal(left, right) => {
                let left = self.term(left, depth)?;
                let right = self.term(right, depth)?;
                Some(atom(format!(
                    "{} == {}",
                    operand(left, SHIFT),
                    operand(right, SHIFT)
                )))
            }
            _ if !self.source_mode() => None,
            Proposition::Predicate { name, arguments } => {
                let surface = crate::kernel::CFunctionContract::surface_name_from_predicate(name)
                    .map(str::to_owned)
                    .or_else(|| {
                        name.strip_prefix("__click_volatile_write_")
                            .map(|event| format!("volatile_write_event_{event}"))
                    })
                    .unwrap_or_else(|| name.clone());
                let mut spelled_arguments = Vec::new();
                for argument in arguments {
                    // A predicate's state argument is implicit in Click.
                    if matches!(argument, Term::CMemory(_) | Term::CState(_)) {
                        continue;
                    }
                    spelled_arguments.push(self.term(argument, depth)?.text);
                }
                Some(atom(format!("{surface}({})", spelled_arguments.join(", "))))
            }
            Proposition::ForAll { var, sort, body } => {
                let sort = self.sort(sort);
                let name = self.binder(*var);
                let body = self.proposition(body, depth);
                self.bound.pop();
                Some(atom(format!(
                    "forall ({name}: {sort}) {{ {} }}",
                    body?.text
                )))
            }
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } => {
                let sort = self.sort(sort);
                let binder = if name.is_empty() {
                    self.binder(*var)
                } else {
                    self.bound.push((*var, name.clone()));
                    name.clone()
                };
                let body = self.proposition(body, depth);
                self.bound.pop();
                Some(atom(format!(
                    "exists ({binder}: {sort}) {{ {} }}",
                    body?.text
                )))
            }
            // Viewability is about an object's extent and lifetime, not the
            // values in its cells, so the memory it was checked in is not
            // part of its spelling.
            Proposition::CMemoryLoadable {
                base, bytes, wide, ..
            } => Some(atom(format!(
                "viewable({})",
                self.byte_range(base, bytes, *wide, depth)
            ))),
            Proposition::CMemoryCanStore {
                pointer,
                byte_width,
                ..
            } => {
                let place = self.place_at(pointer, depth);
                Some(atom(format!("<{place} is writable ({byte_width} bytes)>")))
            }
            Proposition::CMemoryReadDefined {
                memory, pointer, ..
            } => {
                let place = atom(self.place_at(pointer, depth));
                let place = self.qualify(memory, place)?;
                Some(atom(format!("defined({})", place.text)))
            }
            // Retain the exact internal rendering for these object-model
            // facts until this source printer can preserve all their fields.
            Proposition::CValidPlace { .. } | Proposition::CMemoryInitialized { .. } => None,
            Proposition::CMemoryLoads { pointer, .. } => {
                let place = self.place_at(pointer, depth);
                Some(atom(format!("<the read of {place}>")))
            }
            Proposition::CResourceSeparate { left, right } => Some(atom(format!(
                "separate({}, {})",
                self.resource(left),
                self.resource(right)
            ))),
            Proposition::CResourceContains { parent, child } => Some(atom(format!(
                "<{} contains {}>",
                self.resource(parent),
                self.resource(child)
            ))),
            Proposition::CResourceComposition(context) => {
                const LIMIT: usize = 8;
                let (count, entries) = context.diagnostic_facts(LIMIT);
                let tables = self.labels.naming.clone();
                let (parameters, arguments) = tables
                    .as_deref()
                    .map_or((&[][..], &[][..]), |(p, a)| (p.as_slice(), a.as_slice()));
                let mut held = entries
                    .map(|fact| {
                        crate::surface::diagnostics::describe_resource_fact(
                            fact,
                            ParameterBinding::new(parameters, arguments),
                        )
                    })
                    .collect::<Vec<_>>();
                if count > LIMIT {
                    held.push(format!("… {} more", count - LIMIT));
                }
                Some(atom(format!("<held together: {}>", held.join(", "))))
            }
            Proposition::CMemoryMutatesOnly {
                before,
                after,
                writes,
            } => {
                let written = writes
                    .iter()
                    .take(8)
                    .map(|(pointer, _)| self.place_at(pointer, depth))
                    .collect::<Vec<_>>()
                    .join(", ");
                let more = if writes.len() > 8 { ", …" } else { "" };
                let before = self.state_phrase(before);
                let after = self.state_phrase(after);
                Some(atom(format!(
                    "<only {written}{more} changed between {before} and {after}>"
                )))
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                let before = self.state_phrase(before);
                let after = self.state_phrase(after);
                Some(atom(format!(
                    "<{} written range(s) between {before} and {after}>",
                    mutable_ranges.len()
                )))
            }
            Proposition::CHeapAllocationFreed {
                before,
                after,
                allocation_base,
                ..
            } => {
                let base = self.pointer(allocation_base, depth)?.text;
                let before = self.state_phrase(before);
                let after = self.state_phrase(after);
                Some(atom(format!("<{base} freed between {before} and {after}>")))
            }
            Proposition::CExpressionEvaluates { .. }
            | Proposition::CConditionEvaluates { .. }
            | Proposition::CStatementExecutes { .. }
            | Proposition::CStatementVerifies { .. }
            | Proposition::CFunctionExecutes { .. }
            | Proposition::CFunctionVerifies { .. } => {
                Some(atom("<a fact about executing C code>"))
            }
            Proposition::CFunctionSatisfiesSpecification { .. }
            | Proposition::CFunctionPartiallySatisfiesSpecification { .. } => {
                Some(atom("<a function satisfies its specification>"))
            }
        }
    }

    fn sort(&self, sort: &Sort) -> String {
        match sort {
            Sort::Condition => "bool".into(),
            Sort::Bitvector32 | Sort::CInt32 => "int32".into(),
            Sort::Bitvector64 | Sort::CInt64 => "int64".into(),
            Sort::Integer => "Integer".into(),
            Sort::CMachineInteger(ty) => machine_type_spelling(*ty).into(),
            Sort::CPointer(ty) => crate::kernel::c_type_spelling(*ty).into(),
            Sort::Algebraic(ty) => algebraic_type_spelling(&ty.name, &ty.arguments),
            other => format!("{other:?}").to_ascii_lowercase(),
        }
    }

    /// A state's role in a sentence: `function entry`, `here`, a recorded
    /// point, or a report-local `<state A>`.
    fn state_phrase(&mut self, memory: &CMemory) -> String {
        let point = self
            .labels
            .source_memory_context(memory)
            .map(|(point, _)| point.to_owned());
        match point.as_deref() {
            Some("current") => "here".into(),
            Some(ENTRY_POINT) => "function entry".into(),
            Some(point) => format!("`{point}`"),
            None => self.labels.state_label(memory),
        }
    }

    fn condition(
        &mut self,
        condition: &ConditionTerm,
        polarity: bool,
        depth: usize,
    ) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        let negate = |text: String, polarity: bool| {
            if polarity {
                atom(text)
            } else {
                negation(atom(text))
            }
        };
        let comparison = |operator: &str, polarity: bool| -> &'static str {
            match (operator, polarity) {
                ("==", true) | ("!=", false) => "==",
                ("==", false) | ("!=", true) => "!=",
                ("<", true) | (">=", false) => "<",
                ("<", false) | (">=", true) => ">=",
                ("<=", true) | (">", false) => "<=",
                _ => ">",
            }
        };
        match condition {
            ConditionTerm::Constant(value) => return Some(atom((value == &polarity).to_string())),
            ConditionTerm::Variable(variable) => {
                let name = match self.variable_name(*variable) {
                    Some(name) => name,
                    None if self.source_mode() => self.unnamed_variable(*variable),
                    None => return None,
                };
                return Some(negate(name, polarity));
            }
            ConditionTerm::PointerEqual(left, right) => {
                if !self.source_mode() {
                    if self.mode == Mode::ExactIdentity
                        && [left, right]
                            .iter()
                            .any(|p| crate::surface::proof_trace::pointer_definition(p).is_some())
                    {
                        return None;
                    }
                    // Without retained pointee types, do not claim two
                    // different named pointers form a well-typed source
                    // comparison.
                    if left != right && **left != Pointer::null() && **right != Pointer::null() {
                        return None;
                    }
                    let pointer = |p: &Pointer, labels: &SnapshotLabels| {
                        if p == &Pointer::null() {
                            Some("0".to_owned())
                        } else {
                            labels.pointer_sources.get(p).cloned()
                        }
                    };
                    return Some(atom(format!(
                        "{} {} {}",
                        pointer(left, self.labels)?,
                        if polarity { "==" } else { "!=" },
                        pointer(right, self.labels)?
                    )));
                }
                let left = self.pointer(left, depth)?;
                let right = self.pointer(right, depth)?;
                return Some(atom(format!(
                    "{} {} {}",
                    operand(left, SHIFT),
                    if polarity { "==" } else { "!=" },
                    operand(right, SHIFT)
                )));
            }
            ConditionTerm::PointerOffsetEqual(left, right) => {
                if !self.source_mode() {
                    return None;
                }
                let left = self.offset(left, depth);
                let right = self.offset(right, depth);
                return Some(atom(format!(
                    "{left} {} {right}",
                    if polarity { "==" } else { "!=" }
                )));
            }
            ConditionTerm::AlgebraicEqual(left, right) => {
                let left = self.algebraic(left, depth)?;
                let right = self.algebraic(right, depth)?;
                return Some(atom(format!(
                    "{} {} {}",
                    operand(left, SHIFT),
                    if polarity { "==" } else { "!=" },
                    operand(right, SHIFT)
                )));
            }
            crate::kernel::integer_comparison_condition!(a, b) => {
                let operator = match condition {
                    ConditionTerm::IntegerEqual(..) => "==",
                    ConditionTerm::IntegerNotEqual(..) => "!=",
                    ConditionTerm::IntegerLessThan(..) => "<",
                    ConditionTerm::IntegerLessEqual(..) => "<=",
                    ConditionTerm::IntegerGreaterThan(..) => ">",
                    _ => ">=",
                };
                let left = self.integer(a, depth)?;
                let right = self.integer(b, depth)?;
                return Some(atom(format!(
                    "{} {} {}",
                    operand(left, SHIFT),
                    comparison(operator, polarity),
                    operand(right, SHIFT)
                )));
            }
            ConditionTerm::Float32(float) | ConditionTerm::Float64(float) => {
                if !self.source_mode() {
                    return None;
                }
                return match float {
                    crate::kernel::CFloatCondition::Comparison {
                        operator,
                        left,
                        right,
                    } => {
                        use crate::kernel::CComparisonOperator as C;
                        let symbol = match operator {
                            C::Equal => "==",
                            C::NotEqual => "!=",
                            C::LessThan => "<",
                            C::LessEqual => "<=",
                            C::GreaterThan => ">",
                            C::GreaterEqual => ">=",
                        };
                        let left = self.bitvector(left, None, depth)?;
                        let right = self.bitvector(right, None, depth)?;
                        // A float comparison with a NaN operand is false
                        // either way, so its negation keeps the `not`.
                        Some(negate(
                            format!(
                                "{} {symbol} {}",
                                operand(left, SHIFT),
                                operand(right, SHIFT)
                            ),
                            polarity,
                        ))
                    }
                    crate::kernel::CFloatCondition::Classification {
                        classification,
                        value,
                    } => {
                        let value = self.bitvector(value, None, depth)?;
                        Some(negate(
                            format!(
                                "is{}({})",
                                format!("{classification:?}").to_ascii_lowercase(),
                                value.text
                            ),
                            polarity,
                        ))
                    }
                };
            }
            _ => {}
        }
        let (operator, left, right) = condition.as_bitvector_comparison()?;
        let symbol = operator.c_symbol();
        if operator.is_overflow() {
            return self.overflow(condition, operator, left, right, polarity, depth);
        }
        let operator_text = comparison(symbol, polarity);
        let operand_type = operator.operand_type();
        // Lowered unsigned 32-bit order flips both sign bits. Recover the
        // comparison and spell its operands as `uint32` values.
        const SIGN: u32 = 0x8000_0000;
        fn flipped(value: &Bitvector32Term) -> Option<&Bitvector32Term> {
            const SIGN: u32 = 0x8000_0000;
            match value {
                Bitvector32Term::BitwiseXor(a, b) if b.as_const() == Some(SIGN) => Some(a.as_ref()),
                Bitvector32Term::BitwiseXor(a, b) if a.as_const() == Some(SIGN) => Some(b.as_ref()),
                _ => None,
            }
        }
        let is_equality = symbol == "==";
        if operand_type == "int32"
            && !is_equality
            && (flipped(left).is_some() || flipped(right).is_some())
        {
            let recover = |value: &Bitvector32Term| {
                flipped(value).cloned().or_else(|| {
                    value
                        .as_const()
                        .map(|v| Bitvector32Term::Constant(v ^ SIGN))
                })
            };
            let (left, right) = (recover(left)?, recover(right)?);
            if !self.source_mode() {
                return Some(atom(format!(
                    "{} {operator_text} {} (unsigned)",
                    self.exact_operand(&left, Some(false), depth)?,
                    self.exact_operand(&right, Some(false), depth)?
                )));
            }
            let left = self.as_type(&left, Hint::Unsigned32, depth)?;
            let right = self.as_type(&right, Hint::Unsigned32, depth)?;
            return Some(atom(format!(
                "{} {operator_text} {}",
                operand(left, SHIFT),
                operand(right, SHIFT)
            )));
        }
        if !self.source_mode() {
            if operand_type == "bits64" {
                return None;
            }
            let signed = if is_equality {
                [left, right].iter().find_map(|term| {
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
            return Some(atom(format!(
                "{} {operator_text} {}",
                self.exact_operand(left, signed, depth)?,
                self.exact_operand(right, signed, depth)?
            )));
        }
        let (left, right) = match operand_type {
            "int64" => (
                self.as_type(left, Hint::Int64, depth)?,
                self.as_type(right, Hint::Int64, depth)?,
            ),
            "uint64" => (
                self.as_type(left, Hint::UInt64, depth)?,
                self.as_type(right, Hint::UInt64, depth)?,
            ),
            "int32" if !is_equality => (
                self.as_type(left, Hint::Signed32, depth)?,
                self.as_type(right, Hint::Signed32, depth)?,
            ),
            _ => {
                // An equality reads its operands in whichever type one of
                // them shows, signed by default.
                let hint = self.hint_of(left).or_else(|| self.hint_of(right));
                let hint = if operand_type == "int32" {
                    hint.or(Some(Hint::Signed32))
                } else {
                    hint
                };
                (
                    self.bitvector(left, hint, depth)?,
                    self.bitvector(right, hint, depth)?,
                )
            }
        };
        Some(atom(format!(
            "{} {operator_text} {}",
            operand(left, SHIFT),
            operand(right, SHIFT)
        )))
    }

    /// An overflow test is the negation of `defined(a op b)`; a constant
    /// right operand reads as the bound it puts on the left one.
    fn overflow(
        &mut self,
        condition: &ConditionTerm,
        operator: crate::kernel::BitvectorComparisonOp,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
        polarity: bool,
        depth: usize,
    ) -> Option<Spelled> {
        if let (
            ConditionTerm::Bitvector32SignedAddOverflows(..)
            | ConditionTerm::Bitvector32SignedSubtractOverflows(..),
            Bitvector32Term::Constant(bits),
        ) = (condition, b)
        {
            let offset = *bits as i32 as i64;
            if offset == 0 {
                return Some(atom((!polarity).to_string()));
            }
            let addition = matches!(condition, ConditionTerm::Bitvector32SignedAddOverflows(..));
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
            let value = self.bitvector(a, Some(Hint::Signed32), depth)?;
            return Some(atom(format!("{} {op} {bound}", operand(value, SHIFT))));
        }
        if !self.source_mode() {
            return None;
        }
        let hint = if operator.operand_type() == "int64" {
            Hint::Int64
        } else {
            Hint::Signed32
        };
        let precedence = match operator.c_symbol() {
            "+" | "-" => ADD,
            "<<" => SHIFT,
            _ => MULTIPLY,
        };
        let left = self.bitvector(a, Some(hint), depth)?;
        let right = self.bitvector(b, Some(hint), depth)?;
        let operation = format!(
            "{} {} {}",
            operand(left, precedence),
            operator.c_symbol(),
            operand(right, precedence + 1)
        );
        Some(if polarity {
            spelled(format!("not defined({operation})"), NOT)
        } else {
            atom(format!("defined({operation})"))
        })
    }

    /// The exact policy's operand spelling, kept for proof traces.
    fn exact_operand(
        &mut self,
        value: &Bitvector32Term,
        signed: Option<bool>,
        depth: usize,
    ) -> Option<String> {
        if signed == Some(true) && matches!(value, Bitvector32Term::UInt32From64(_)) {
            let value = self.bitvector(value, None, depth)?;
            return Some(cast("int32", value).text);
        }
        if let Bitvector32Term::Constant(value) = value {
            return match signed {
                Some(true) => Some((*value as i32).to_string()),
                Some(false) => Some(value.to_string()),
                None if *value <= i32::MAX as u32 => Some(value.to_string()),
                None => None,
            };
        }
        self.bitvector(value, None, depth)
            .map(|value| operand(value, SHIFT))
    }

    /// `value` read as `hint`: a constant written in that type and any
    /// other operand of another known type converted with a cast.
    fn as_type(&mut self, value: &Bitvector32Term, hint: Hint, depth: usize) -> Option<Spelled> {
        let literal = matches!(
            value,
            Bitvector32Term::Constant(_)
                | Bitvector32Term::Int64Constant(_)
                | Bitvector32Term::UInt64Constant(_)
        );
        let own = self.hint_of(value);
        let needs_cast = !literal
            && match (hint, own) {
                // An operand of unknown type in an unsigned order is shown
                // converted, since an `int32` reading is the default.
                (Hint::Unsigned32, None) => true,
                (_, None) => false,
                (Hint::Signed32, Some(Hint::Narrow { .. })) => false,
                (Hint::Unsigned32, Some(Hint::Narrow { signed: false })) => false,
                (wanted, Some(own)) => wanted != own,
            };
        // A value of unknown type shown converted keeps its own constants
        // plain: `(uint32)(x + 1)`.
        let inner_hint = if hint == Hint::Unsigned32 && own.is_none() && !literal {
            None
        } else {
            Some(hint)
        };
        let spelled_value = match value {
            // A constant in a 64-bit comparison is written in that type.
            Bitvector32Term::Int64Constant(bits) if hint == Hint::UInt64 => {
                atom(format!("{}u64", *bits as u64))
            }
            Bitvector32Term::UInt64Constant(bits) if hint == Hint::Int64 => {
                atom(format!("{}i64", *bits as i64))
            }
            _ => self.bitvector(value, inner_hint, depth)?,
        };
        if !needs_cast {
            return Some(spelled_value);
        }
        let name = match hint {
            Hint::Signed32 => "int32",
            Hint::Unsigned32 => "uint32",
            Hint::Int64 => "int64",
            Hint::UInt64 => "uint64",
            Hint::Narrow { .. } => return Some(spelled_value),
        };
        Some(cast(name, spelled_value))
    }

    /// The source type of a term, where it shows.
    fn hint_of(&self, value: &Bitvector32Term) -> Option<Hint> {
        use Bitvector32Term as B;
        match value {
            B::Int64Constant(_) => Some(Hint::Int64),
            B::UInt64Constant(_) => Some(Hint::UInt64),
            B::Variable(variable) => self
                .labels
                .source_types
                .get(variable)
                .and_then(|ty| Hint::of_type(*ty))
                .or_else(|| {
                    crate::kernel::registered_load_kind_for_variable(variable)
                        .and_then(Hint::of_load)
                }),
            B::MemoryLoad(_, _, kind) => Hint::of_load(*kind),
            B::Int64From32(_) | B::Int64FromUInt32(_) => Some(Hint::Int64),
            B::UInt64From32(_) | B::UInt64FromInt32(_) | B::UInt64FromInt64(_) => {
                Some(Hint::UInt64)
            }
            B::UInt32From64(_) => Some(Hint::Unsigned32),
            B::MachineIntegerCast { destination, .. } | B::IntegerToMachine { destination, .. } => {
                Hint::of_machine(*destination)
            }
            B::If {
                then_term,
                else_term,
                ..
            } => self.hint_of(then_term).or_else(|| self.hint_of(else_term)),
            B::Int64BitwiseNot(_) => Some(Hint::Int64),
            B::UInt64BitwiseNot(_) => Some(Hint::UInt64),
            B::BitwiseNot(inner) => self.hint_of(inner),
            _ => {
                let (operator, left, right) = value.as_binary()?;
                use crate::kernel::BitvectorBinaryOp as Op;
                match operator {
                    Op::Int64Add
                    | Op::Int64Subtract
                    | Op::Int64Multiply
                    | Op::Int64Divide
                    | Op::Int64Remainder
                    | Op::Int64ShiftLeft
                    | Op::Int64ArithmeticShiftRight
                    | Op::Int64BitwiseAnd
                    | Op::Int64BitwiseOr
                    | Op::Int64BitwiseXor => Some(Hint::Int64),
                    Op::UInt64Add
                    | Op::UInt64Subtract
                    | Op::UInt64Multiply
                    | Op::UInt64Divide
                    | Op::UInt64Remainder
                    | Op::UInt64ShiftLeft
                    | Op::UInt64LogicalShiftRight
                    | Op::UInt64BitwiseAnd
                    | Op::UInt64BitwiseOr
                    | Op::UInt64BitwiseXor => Some(Hint::UInt64),
                    Op::UnsignedDivide | Op::UnsignedRemainder | Op::LogicalShiftRight => {
                        Some(Hint::Unsigned32)
                    }
                    _ if operator.is_float() => None,
                    _ => self.hint_of(left).or_else(|| self.hint_of(right)),
                }
            }
        }
    }

    fn constant(&self, value: u32, hint: Option<Hint>) -> Option<Spelled> {
        match hint {
            Some(Hint::Unsigned32) if self.source_mode() => {
                Some(atom(typed_literal(value.to_string(), "u32")))
            }
            Some(Hint::Narrow { signed: false }) | Some(Hint::Unsigned32) => {
                Some(atom(value.to_string()))
            }
            _ if self.source_mode() || value <= i32::MAX as u32 => {
                let value = value as i32;
                Some(if value < 0 {
                    spelled(value.to_string(), UNARY)
                } else {
                    atom(value.to_string())
                })
            }
            _ => None,
        }
    }

    fn term(&mut self, term: &Term, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        match term {
            Term::Bitvector32(value) => self.bitvector(value, None, depth + 1),
            Term::Integer(value) => self.integer(value, depth + 1),
            Term::Condition(ConditionTerm::Constant(value)) => Some(atom(value.to_string())),
            Term::CValue(value) => self.cvalue(value, depth + 1),
            Term::Algebraic(value) => self.algebraic(value, depth + 1),
            _ if !self.source_mode() => None,
            Term::Condition(condition) => self.condition(condition, true, depth + 1),
            Term::PointerOffset(offset) => Some(atom(self.offset(offset, depth + 1))),
            Term::CMemory(memory) => Some(atom(self.state_phrase(memory))),
            Term::CState(state) => Some(atom(self.state_phrase(state.memory()))),
            Term::CExpressionOutcome(_)
            | Term::CStatementOutcome(_)
            | Term::CFunctionOutcome(_) => Some(atom("<an execution outcome>")),
            Term::Sequence(_) => Some(atom("<a sequence>")),
        }
    }

    fn offset(&mut self, offset: &PointerOffsetTerm, depth: usize) -> String {
        match offset {
            PointerOffsetTerm::Constant(bytes) => bytes.to_string(),
            PointerOffsetTerm::Variable(variable) => self
                .variable_name(*variable)
                .unwrap_or_else(|| self.unnamed_variable(*variable)),
            PointerOffsetTerm::Add(left, right) => format!(
                "{} + {}",
                self.offset(left, depth + 1),
                self.offset(right, depth + 1)
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width }
            | PointerOffsetTerm::Int64Scaled {
                value, byte_width, ..
            } => {
                let value = self
                    .bitvector(value, None, depth + 1)
                    .map_or_else(|| "…".into(), |value| operand(value, MULTIPLY));
                if *byte_width == 1 {
                    value
                } else {
                    format!("{value} * {byte_width}")
                }
            }
        }
    }

    fn bitvector(
        &mut self,
        value: &Bitvector32Term,
        hint: Option<Hint>,
        depth: usize,
    ) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        use Bitvector32Term as B;
        match value {
            B::Constant(value) => return self.constant(*value, hint),
            B::Int64Constant(value) => return Some(atom(format!("{value}i64"))),
            B::UInt64Constant(value) => return Some(atom(format!("{value}u64"))),
            B::Variable(variable) => {
                if self.mode == Mode::ExactIdentity && crate::kernel::is_load_variable(variable) {
                    return None;
                }
                if let Some(name) = self.variable_name(*variable) {
                    return Some(atom(name));
                }
                if let Some((memory, pointer)) =
                    crate::kernel::registered_load_for_variable(variable)
                {
                    return self.load(
                        memory.memory(),
                        &pointer,
                        crate::kernel::registered_load_kind_for_variable(variable)?,
                        depth,
                    );
                }
                if let Some(field) = crate::kernel::model_fields::model_field_spelling(*variable) {
                    return Some(atom(field));
                }
                return self.placeholder(|printer| printer.unnamed_variable(*variable));
            }
            B::MemoryLoad(memory, pointer, kind) => {
                return self.load(memory.as_ref(), pointer, *kind, depth);
            }
            B::UInt32From64(inner) if !self.source_mode() => {
                let inner = self.bitvector(inner, None, depth)?;
                return Some(cast("uint32", inner));
            }
            _ => {}
        }
        if let Some((operator, left, right)) = value.as_binary() {
            if !self.source_mode()
                && !matches!(
                    value,
                    B::Add(..)
                        | B::Subtract(..)
                        | B::Multiply(..)
                        | B::UInt64Add(..)
                        | B::UInt64Subtract(..)
                        | B::UInt64Multiply(..)
                        | B::UInt64Divide(..)
                        | B::UInt64Remainder(..)
                )
            {
                return None;
            }
            let symbol = operator.c_symbol();
            let precedence = match symbol {
                "*" | "/" | "%" => MULTIPLY,
                "+" | "-" => ADD,
                "<<" | ">>" => SHIFT,
                "&" => BITWISE_AND,
                "^" => BITWISE_XOR,
                _ => BITWISE_OR,
            };
            let operand_hint = self.hint_of(value).or(hint);
            // The right operand of a shift is a count, not a value of the
            // shifted type.
            let right_hint = if precedence == SHIFT {
                None
            } else {
                operand_hint
            };
            let left = self.bitvector(left, operand_hint, depth)?;
            let right = self.bitvector(right, right_hint, depth)?;
            return Some(spelled(
                format!(
                    "{} {symbol} {}",
                    operand(left, precedence),
                    operand(right, precedence + 1)
                ),
                precedence,
            ));
        }
        if !self.source_mode() {
            return None;
        }
        if let Some((operator, inner)) = value.as_unary() {
            use crate::kernel::BitvectorUnaryOp as U;
            let (prefix, type_name) = match operator {
                U::BitwiseNot | U::Int64BitwiseNot | U::UInt64BitwiseNot => (Some("~"), None),
                U::Float32Negate | U::Float64Negate => (Some("-"), None),
                U::Int64From32 | U::Int64FromUInt32 => (None, Some("int64")),
                U::UInt64From32 | U::UInt64FromInt32 | U::UInt64FromInt64 => (None, Some("uint64")),
                U::UInt32From64 => (None, Some("uint32")),
                U::MachineIntegerCast { destination, .. } => {
                    (None, Some(machine_type_spelling(destination)))
                }
            };
            let inner_hint = match operator {
                U::BitwiseNot | U::Int64BitwiseNot | U::UInt64BitwiseNot => hint,
                U::Int64FromUInt32 | U::UInt64From32 => Some(Hint::Unsigned32),
                U::Int64From32 | U::UInt64FromInt32 => Some(Hint::Signed32),
                U::UInt64FromInt64 => Some(Hint::Int64),
                U::MachineIntegerCast { source, .. } => Hint::of_machine(source),
                _ => None,
            };
            let inner = self.bitvector(inner, inner_hint, depth)?;
            return Some(match (prefix, type_name) {
                (Some(prefix), _) => spelled(format!("{prefix}{}", operand(inner, UNARY)), UNARY),
                (None, Some(name)) => cast(name, inner),
                (None, None) => inner,
            });
        }
        match value {
            B::MachineIntegerConstant(value) => Some(atom(format!(
                "{}{}128",
                value.to_integer(),
                if value.format().is_signed() { "i" } else { "u" }
            ))),
            B::If {
                condition,
                then_term,
                else_term,
            } => {
                let condition = self.condition(condition, true, depth)?;
                let then_term = self.bitvector(then_term, hint, depth)?;
                let else_term = self.bitvector(else_term, hint, depth)?;
                // Parenthesized wherever it is an operand, for the reader.
                Some(spelled(
                    format!(
                        "if {} {{ {} }} else {{ {} }}",
                        condition.text, then_term.text, else_term.text
                    ),
                    0,
                ))
            }
            B::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                let start = self.bitvector(start, None, depth)?;
                let end = self.bitvector(end, None, depth)?;
                let initial = self.bitvector(initial, hint, depth)?;
                self.bound.push((*accumulator, "acc".into()));
                self.bound.push((*item, "k".into()));
                let body = self.bitvector(body, hint, depth);
                self.bound.pop();
                self.bound.pop();
                Some(atom(format!(
                    "({}..{}).fold({}, |acc, k| {{ {} }})",
                    operand(start, ADD),
                    operand(end, ADD),
                    initial.text,
                    body?.text
                )))
            }
            B::PureFunctionApplication { name, arguments } => {
                let mut spelled_arguments = Vec::new();
                for argument in arguments {
                    spelled_arguments.push(self.bitvector(argument, None, depth)?.text);
                }
                Some(atom(format!("{name}({})", spelled_arguments.join(", "))))
            }
            B::ClickFunctionApplication { name, arguments } => self.call(name, arguments, depth),
            B::AlgebraicMatch { scrutinee, arms } => {
                let scrutinee = self.algebraic(scrutinee, depth)?;
                let mut spelled_arms = Vec::new();
                for arm in arms {
                    let body = self.bitvector(&arm.body, hint, depth)?;
                    spelled_arms.push(format!("{} => {}", arm.variant, body.text));
                }
                Some(atom(format!(
                    "match {} {{ {} }}",
                    scrutinee.text,
                    spelled_arms.join(", ")
                )))
            }
            B::PointerAddress(pointer) => {
                let pointer = self.pointer(pointer, depth)?;
                Some(cast("uint64", pointer))
            }
            B::IntegerToMachine { value, destination } => {
                let value = self.integer(value, depth)?;
                Some(atom(format!(
                    "to_{}({})",
                    machine_type_spelling(*destination),
                    value.text
                )))
            }
            _ => self.placeholder(|_| "<value>".into()),
        }
    }

    /// The place `pointer` addresses, without a state qualifier: a source
    /// cell where the naming tables have one, else a dereference.
    fn place_at(&mut self, pointer: &Pointer, depth: usize) -> String {
        if let Some(referent) = self.reference_referent(pointer) {
            return referent;
        }
        let tables = self.labels.naming.clone();
        if let Some((parameters, arguments)) = tables.as_deref()
            && let Some(cell) = crate::surface::diagnostics::diagnostic_source_cell(
                pointer,
                ParameterBinding::new(parameters, arguments),
            )
        {
            return cell;
        }
        match self.pointer(pointer, depth) {
            Some(address) => dereference(address),
            None => "…".into(),
        }
    }

    fn load(
        &mut self,
        memory: &CMemory,
        pointer: &Pointer,
        kind: crate::kernel::LoadKind,
        depth: usize,
    ) -> Option<Spelled> {
        if self.mode == Mode::ExactIdentity {
            return None;
        }
        let context = self
            .labels
            .source_memory_context(memory)
            .map(|(point, naming)| (point.len() <= 256, std::rc::Rc::new(naming.clone())));
        if !self.source_mode() && context.is_none() {
            return None;
        }
        if self.source_mode()
            && let Some(referent) = self.reference_referent(pointer)
        {
            return self.qualify(memory, atom(referent));
        }
        let naming = match &context {
            Some((true, naming)) => Some(naming.clone()),
            Some((false, _)) => return None,
            None => self.labels.naming.clone(),
        };
        let cell = naming.as_deref().and_then(|naming| {
            // An address spelling alone does not establish the type of a
            // read. Keep only bases whose declared element has this exact
            // load kind.
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
            crate::surface::diagnostics::diagnostic_source_load_cell(
                pointer,
                kind,
                ParameterBinding::new(&names, &values),
            )
        });
        let place = match cell {
            Some(cell) if !(self.source_mode() && cell.contains('+')) => atom(cell),
            None if !self.source_mode() => return None,
            _ => {
                let address = self.pointer(pointer, depth)?;
                if let Some(place) = address.text.strip_prefix("the caller's ") {
                    // A by-value aggregate argument's field is a place of
                    // the caller's.
                    atom(format!("the caller's {place}"))
                } else if address.text.starts_with("(char *)") && kind.byte_width() != 1 {
                    // A read at a byte offset reads the load's own type.
                    atom(format!(
                        "*({} *)({})",
                        load_type_spelling(kind)?,
                        address.text
                    ))
                } else {
                    atom(dereference(address))
                }
            }
        };
        self.qualify(memory, place)
    }

    /// `place` read in `memory`.
    fn qualify(&mut self, memory: &CMemory, place: Spelled) -> Option<Spelled> {
        let point = self
            .labels
            .source_memory_context(memory)
            .map(|(point, _)| point.to_owned());
        Some(match point.as_deref() {
            Some("current") => place,
            Some(ENTRY_POINT) => atom(format!("old({})", place.text)),
            Some(point) => atom(format!("at({point}, {})", place.text)),
            None if self.source_mode() => {
                let state = self.labels.state_label(memory);
                atom(format!("at({state}, {})", place.text))
            }
            None => return None,
        })
    }

    /// An address in source terms.
    fn pointer(&mut self, pointer: &Pointer, depth: usize) -> Option<Spelled> {
        if pointer == &Pointer::null() {
            return Some(atom("0"));
        }
        if let Some(name) = self.labels.pointer_sources.get(pointer) {
            // A reference parameter's carrier is spelled `&value`.
            let precedence = if name.starts_with('&') { UNARY } else { ATOM };
            return Some(spelled(name.clone(), precedence));
        }
        if !self.source_mode() {
            return None;
        }
        // A pointer read from memory is the place it was read from.
        if let Some(read) = pointer.as_loaded_value() {
            let place =
                self.pointer_cell(read.defining_memory.memory(), &read.defining_address, depth);
            return Some(if read.displacement == PointerOffsetTerm::Constant(0) {
                place
            } else {
                let offset = self.offset(&read.displacement, depth);
                atom(format!("byte_offset({}, {offset})", place.text))
            });
        }
        if let Some(Bitvector32Term::MemoryLoad(memory, address, _)) =
            crate::kernel::logical_pointer_read_term(pointer)
        {
            return Some(self.pointer_cell(memory.memory(), &address, depth));
        }
        let tables = self.labels.naming.clone();
        if let Some((parameters, arguments)) = tables.as_deref() {
            let binding = ParameterBinding::new(parameters, arguments);
            if let Some(cell) =
                crate::surface::diagnostics::diagnostic_source_cell(pointer, binding)
                && !cell.contains('+')
            {
                return Some(spelled(format!("&{cell}"), UNARY));
            }
            let address = crate::surface::diagnostics::describe_pointer(pointer, binding);
            if !address.contains("the pointer value at this program point")
                && !address.contains('…')
            {
                let precedence = if address
                    .chars()
                    .all(|c| c.is_alphanumeric() || "_.[]&".contains(c))
                {
                    if address.starts_with('&') {
                        UNARY
                    } else {
                        ATOM
                    }
                } else {
                    0
                };
                return Some(spelled(address, precedence));
            }
        }
        Some(atom(self.labels.unnamed_pointer(pointer)))
    }

    /// The pointer stored at `address` in `memory`, as the place it is read
    /// from.
    fn pointer_cell(&mut self, memory: &CMemory, address: &Pointer, depth: usize) -> Spelled {
        let tables = self.labels.naming.clone();
        let cell = tables.as_deref().and_then(|(parameters, arguments)| {
            let binding = ParameterBinding::new(parameters, arguments);
            crate::surface::diagnostics::diagnostic_source_pointer_cell(address, binding, None)
                .or_else(|| crate::surface::diagnostics::diagnostic_source_cell(address, binding))
        });
        let place = match cell {
            Some(cell) => atom(cell),
            None => match self.pointer(address, depth) {
                Some(address) => atom(dereference(address)),
                None => atom("…"),
            },
        };
        self.qualify(memory, place).unwrap_or_else(|| atom("…"))
    }

    /// A byte range as Click writes a viewable range: in elements of the
    /// base's declared type when its width divides the byte count, and in
    /// bytes otherwise.
    fn byte_range(
        &mut self,
        base: &Pointer,
        bytes: &Bitvector32Term,
        wide: bool,
        depth: usize,
    ) -> String {
        let referent = self.reference_referent(base);
        let address = self.pointer(base, depth).unwrap_or_else(|| atom("…"));
        let hint = if wide {
            Some(Hint::UInt64)
        } else {
            Some(Hint::Signed32)
        };
        // A range from an element of a named pointer, `&p[i]`, reads as
        // `p[i..i + n]`.
        let element = address
            .text
            .strip_prefix('&')
            .and_then(|place| place.strip_suffix(']'))
            .and_then(|place| place.split_once('['))
            .filter(|(name, _)| name.chars().all(|c| c.is_alphanumeric() || c == '_'))
            .and_then(|(name, index)| {
                Some((
                    name.to_owned(),
                    index.to_owned(),
                    self.named_element_width(name)?,
                ))
            });
        let width = match &element {
            Some((_, _, width)) => Some(*width),
            None => self.element_width(base),
        };
        let count = match width {
            Some(1) => self.bitvector(bytes, hint, depth),
            Some(width) => match bytes {
                Bitvector32Term::Constant(value) if i64::from(*value) % width == 0 => {
                    Some(atom((i64::from(*value) / width).to_string()))
                }
                Bitvector32Term::UInt64Constant(value) if (*value as i64) % width == 0 => {
                    Some(atom(format!("{}u64", *value as i64 / width)))
                }
                Bitvector32Term::Multiply(left, right)
                | Bitvector32Term::UInt64Multiply(left, right)
                    if right.as_const().map(i64::from) == Some(width) =>
                {
                    self.bitvector(left, hint, depth)
                }
                Bitvector32Term::Multiply(left, right)
                | Bitvector32Term::UInt64Multiply(left, right)
                    if left.as_const().map(i64::from) == Some(width) =>
                {
                    self.bitvector(right, hint, depth)
                }
                _ => None,
            },
            None => None,
        };
        match (count, element) {
            // The whole referent of a reference parameter is the referent.
            (Some(count), _) if referent.is_some() && count.text == "1" => {
                referent.unwrap_or_default()
            }
            (Some(count), Some((name, index, _))) => {
                let end = match (index.parse::<i64>(), count.text.parse::<i64>()) {
                    (Ok(index), Ok(count)) => (index + count).to_string(),
                    _ => format!("{index} + {}", operand(count, ADD + 1)),
                };
                format!("{name}[{index}..{end}]")
            }
            (Some(count), None) => format!("{}[0..{}]", operand(address, ATOM), count.text),
            (None, _) => {
                let bytes = self
                    .bitvector(bytes, hint, depth)
                    .map_or_else(|| "…".into(), |bytes| bytes.text);
                format!("((uint8 *){})[0..{bytes}]", operand(address, UNARY))
            }
        }
    }

    /// The referent a C++ reference parameter names when `pointer` is the
    /// address it carries: `value` for `int32& value`, and the field at its
    /// start for a struct referent. The sidecar writes the referent, never
    /// the carrier.
    fn reference_referent(&self, pointer: &Pointer) -> Option<String> {
        let tables = self.labels.naming.as_deref()?;
        tables
            .0
            .iter()
            .zip(&tables.1)
            .find_map(|(parameter, value)| {
                let crate::kernel::CExpression::Value(crate::kernel::CValue::Pointer(base)) = value
                else {
                    return None;
                };
                if !parameter.is_reference() || base.pointer() != pointer {
                    return None;
                }
                let referent = crate::languages::c::syntax::referent_of_carrier(parameter.name())?;
                match parameter
                    .pointee_struct_layout()
                    .or_else(|| parameter.struct_layout())
                {
                    None => Some(referent.to_owned()),
                    Some(layout) => layout
                        .leaf_field_offsets()
                        .find(|(_, offset)| *offset == 0)
                        .map(|(field, _)| format!("{referent}.{field}")),
                }
            })
    }

    /// The element width of the pointer parameter or local called `name`.
    fn named_element_width(&self, name: &str) -> Option<i64> {
        let tables = self.labels.naming.as_deref()?;
        tables
            .0
            .iter()
            .zip(&tables.1)
            .find_map(|(parameter, value)| match value {
                crate::kernel::CExpression::Value(crate::kernel::CValue::Pointer(_))
                    if parameter.name() == name =>
                {
                    Some(crate::surface::diagnostics::diagnostic_parameter_element_width(parameter))
                }
                _ => None,
            })
            .filter(|width| *width > 0)
    }

    /// The element width of the pointer a naming table binds to `base`.
    fn element_width(&self, base: &Pointer) -> Option<i64> {
        let tables = self.labels.naming.as_deref()?;
        tables
            .0
            .iter()
            .zip(&tables.1)
            .find_map(|(parameter, value)| match value {
                crate::kernel::CExpression::Value(crate::kernel::CValue::Pointer(pointer))
                    if pointer.pointer() == base =>
                {
                    Some(crate::surface::diagnostics::diagnostic_parameter_element_width(parameter))
                }
                _ => None,
            })
            .filter(|width| *width > 0)
    }

    fn resource(&mut self, resource: &CResource) -> String {
        let tables = self.labels.naming.clone();
        let (parameters, arguments) = tables
            .as_deref()
            .map_or((&[][..], &[][..]), |(p, a)| (p.as_slice(), a.as_slice()));
        let text = crate::surface::diagnostics::describe_resource_fact(
            &CResourceFact::View(resource.clone()),
            ParameterBinding::new(parameters, arguments),
        );
        text.strip_prefix("views ")
            .map(str::to_owned)
            .unwrap_or(text)
    }

    fn cvalue(&mut self, value: &crate::kernel::CValue, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        use crate::kernel::CValue;
        if let CValue::PointerInteger(value) = value {
            return self.cvalue(&value.numeric_value(), depth);
        }
        if !self.source_mode() {
            return match value {
                CValue::Bool(Bitvector32Term::Constant(0)) => Some(atom("false")),
                CValue::Bool(Bitvector32Term::Constant(1)) => Some(atom("true")),
                CValue::Bool(value) | CValue::Int64(value) | CValue::UInt64(value) => {
                    self.bitvector(value, None, depth)
                }
                CValue::Int32(value) => self
                    .exact_operand(value, Some(true), depth)
                    .map(|text| spelled(text, SHIFT)),
                CValue::UInt32(value) => self
                    .exact_operand(value, Some(false), depth)
                    .map(|text| spelled(text, SHIFT)),
                CValue::Pointer(pointer) => {
                    let naming = self.labels.naming.clone()?;
                    self.exact_pointer_value(pointer, &naming).map(atom)
                }
                _ => None,
            };
        }
        let typed = |printer: &mut Self, value: &Bitvector32Term, hint: Hint, suffix: &str| {
            let spelled_value = printer.bitvector(value, Some(hint), depth)?;
            Some(match value {
                Bitvector32Term::Constant(_) if !suffix.is_empty() => {
                    atom(typed_literal(spelled_value.text, suffix))
                }
                _ => spelled_value,
            })
        };
        match value {
            CValue::PointerInteger(_) => {
                unreachable!("pointer integers render their numeric value")
            }
            CValue::Void => Some(atom("void")),
            CValue::Bool(Bitvector32Term::Constant(0)) => Some(atom("false")),
            CValue::Bool(Bitvector32Term::Constant(1)) => Some(atom("true")),
            CValue::Bool(value) => {
                self.bitvector(value, Some(Hint::Narrow { signed: false }), depth)
            }
            CValue::Int8(value) => typed(self, value, Hint::Narrow { signed: true }, "i8"),
            CValue::Int16(value) => typed(self, value, Hint::Narrow { signed: true }, "i16"),
            CValue::UInt8(value) => typed(self, value, Hint::Narrow { signed: false }, "u8"),
            CValue::UInt16(value) => typed(self, value, Hint::Narrow { signed: false }, "u16"),
            CValue::Int32(value) => typed(self, value, Hint::Signed32, ""),
            CValue::UInt32(value) => typed(self, value, Hint::Unsigned32, ""),
            CValue::Int64(value) => typed(self, value, Hint::Int64, ""),
            CValue::UInt64(value) => typed(self, value, Hint::UInt64, ""),
            CValue::Int128(value) | CValue::UInt128(value) => self.bitvector(value, None, depth),
            CValue::Float32(Bitvector32Term::Constant(bits)) => {
                Some(atom(format!("{:?}f32", f32::from_bits(*bits))))
            }
            CValue::Float64(Bitvector32Term::UInt64Constant(bits)) => {
                Some(atom(format!("{:?}", f64::from_bits(*bits))))
            }
            CValue::Float32(value) | CValue::Float64(value) => self.bitvector(value, None, depth),
            CValue::Pointer(pointer) => self.pointer(pointer.pointer(), depth),
        }
    }

    fn exact_pointer_value(
        &self,
        pointer: &crate::kernel::CPointerValue,
        naming: &NamingTables,
    ) -> Option<String> {
        if self.mode == Mode::ExactIdentity
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

    fn pure_argument(&mut self, argument: &PureFunctionArgument, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        match argument {
            PureFunctionArgument::Value(value) => self.cvalue(value, depth + 1),
            PureFunctionArgument::Integer(value) => self.integer(value, depth + 1),
            PureFunctionArgument::Algebraic(value) => self.algebraic(value, depth + 1),
            PureFunctionArgument::ArrayRef {
                memory,
                pointer: crate::kernel::CValue::Pointer(pointer),
                element_type,
            } => {
                if !self.source_mode() {
                    if pointer.c_type().pointee_type() != Some(*element_type)
                        || self.mode == Mode::ExactIdentity
                    {
                        return None;
                    }
                    let (point, naming) = self.labels.source_memory_context(memory)?;
                    let (point, naming) = (point.to_owned(), naming.clone());
                    let name = self.exact_pointer_value(pointer, &naming)?;
                    return Some(atom(if point == "current" {
                        name
                    } else {
                        format!("at({point}, {name})")
                    }));
                }
                let name = self.pointer(pointer.pointer(), depth + 1)?;
                self.qualify(memory, name)
            }
            PureFunctionArgument::ArrayRef { .. } => self.placeholder(|_| "<array>".into()),
        }
    }

    fn call(
        &mut self,
        name: &str,
        arguments: &[PureFunctionArgument],
        depth: usize,
    ) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        if name.len() > 256 {
            return None;
        }
        let mut spelled_arguments = Vec::new();
        for argument in arguments {
            spelled_arguments.push(self.pure_argument(argument, depth + 1)?.text);
        }
        let text = format!("{name}({})", spelled_arguments.join(", "));
        (text.len() <= 2048 || self.source_mode()).then(|| atom(text))
    }

    fn algebraic(&mut self, value: &AlgebraicTerm, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        match &value.node {
            AlgebraicTermNode::Variable(variable) => match self.variable_name(*variable) {
                Some(name) => Some(atom(name)),
                None => self.placeholder(|printer| printer.unnamed_variable(*variable)),
            },
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                self.call(name, arguments, depth + 1)
            }
            AlgebraicTermNode::Constructor { variant, fields } => {
                if value.algebraic_type.name.len() + variant.len() > 256 {
                    return None;
                }
                let mut spelled_fields = Vec::new();
                for field in fields {
                    spelled_fields.push(
                        match field {
                            AlgebraicValue::C(value) => self.cvalue(value, depth + 1),
                            AlgebraicValue::Integer(value) => self.integer(value, depth + 1),
                            AlgebraicValue::Algebraic(value) => self.algebraic(value, depth + 1),
                        }?
                        .text,
                    );
                }
                let name = format!("{}::{variant}", value.algebraic_type.name);
                Some(atom(if spelled_fields.is_empty() {
                    name
                } else {
                    format!("{name}({})", spelled_fields.join(", "))
                }))
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                if !self.source_mode() {
                    return None;
                }
                let scrutinee = self.algebraic(scrutinee, depth + 1)?;
                let mut spelled_arms = Vec::new();
                for arm in arms {
                    let body = self.algebraic(&arm.body, depth + 1)?;
                    spelled_arms.push(format!("{} => {}", arm.variant, body.text));
                }
                Some(atom(format!(
                    "match {} {{ {} }}",
                    scrutinee.text,
                    spelled_arms.join(", ")
                )))
            }
        }
    }

    fn integer(&mut self, value: &IntegerTerm, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        match value {
            IntegerTerm::Constant(value) if value.bits() <= 256 => {
                let text = value.to_string();
                Some(if text.starts_with('-') {
                    spelled(text, UNARY)
                } else {
                    atom(text)
                })
            }
            IntegerTerm::Constant(value) => {
                self.placeholder(|_| format!("<{}-bit integer>", value.bits()))
            }
            IntegerTerm::Variable(variable) => match self
                .variable_name(*variable)
                .or_else(|| crate::kernel::model_fields::model_field_spelling(*variable))
            {
                Some(name) => Some(atom(name)),
                None => self.placeholder(|printer| printer.unnamed_variable(*variable)),
            },
            IntegerTerm::PureFunctionApplication(application) => {
                self.call(application.name(), application.arguments(), depth)
            }
            IntegerTerm::Negate(value) => {
                let value = self.integer(value, depth)?;
                Some(spelled(format!("-{}", operand(value, UNARY)), UNARY))
            }
            IntegerTerm::Add(a, b) | IntegerTerm::Subtract(a, b) | IntegerTerm::Multiply(a, b) => {
                let (op, precedence) = match value {
                    IntegerTerm::Add(..) => ("+", ADD),
                    IntegerTerm::Subtract(..) => ("-", ADD),
                    _ => ("*", MULTIPLY),
                };
                let left = self.integer(a, depth)?;
                let right = self.integer(b, depth)?;
                Some(spelled(
                    format!(
                        "{} {op} {}",
                        operand(left, precedence),
                        operand(right, precedence + 1)
                    ),
                    precedence,
                ))
            }
            _ if !self.source_mode() => None,
            IntegerTerm::Machine(value) => {
                let hint = Hint::of_machine(value.ty());
                let value = self.bitvector(value.value(), hint, depth)?;
                Some(atom(format!("to_integer({})", value.text)))
            }
            IntegerTerm::TruncatingQuotient(a, b) | IntegerTerm::TruncatingRemainder(a, b) => {
                let op = if matches!(value, IntegerTerm::TruncatingQuotient(..)) {
                    "/"
                } else {
                    "%"
                };
                let left = self.integer(a, depth)?;
                let right = self.integer(b, depth)?;
                Some(spelled(
                    format!(
                        "{} {op} {}",
                        operand(left, MULTIPLY),
                        operand(right, MULTIPLY + 1)
                    ),
                    MULTIPLY,
                ))
            }
            IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
                let scrutinee = self.algebraic(scrutinee, depth)?;
                let mut spelled_arms = Vec::new();
                for arm in arms {
                    let body = self.integer(&arm.body, depth)?;
                    spelled_arms.push(format!("{} => {}", arm.variant, body.text));
                }
                Some(atom(format!(
                    "match {} {{ {} }}",
                    scrutinee.text,
                    spelled_arms.join(", ")
                )))
            }
            IntegerTerm::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => {
                let (start, end) = match index {
                    IntegerRangeFoldIndex::Int32 { start, end }
                    | IntegerRangeFoldIndex::UInt64 { start, end } => (
                        self.bitvector(start.value(), None, depth)?,
                        self.bitvector(end.value(), None, depth)?,
                    ),
                    IntegerRangeFoldIndex::Integer { start, end } => {
                        (self.integer(start, depth)?, self.integer(end, depth)?)
                    }
                };
                let initial = self.integer(initial, depth)?;
                self.bound.push((*accumulator, "acc".into()));
                self.bound.push((*item, "k".into()));
                let body = self.integer(body, depth);
                self.bound.pop();
                self.bound.pop();
                Some(atom(format!(
                    "({}..{}).fold({}, |acc, k| {{ {} }})",
                    operand(start, ADD),
                    operand(end, ADD),
                    initial.text,
                    body?.text
                )))
            }
        }
    }
}

fn load_type_spelling(kind: crate::kernel::LoadKind) -> Option<&'static str> {
    use crate::kernel::LoadKind as K;
    Some(match kind {
        K::Pointer => return None,
        K::Int8 => "int8",
        K::UInt8 => "uint8",
        K::Int16 => "int16",
        K::UInt16 => "uint16",
        K::Bits32 => "int32",
        K::Bits64 => "int64",
        K::Int128 => "int128",
        K::UInt128 => "uint128",
        K::Float32 => "float",
        K::Float64 => "double",
    })
}

fn algebraic_type_spelling(name: &str, arguments: &[AlgebraicValueType]) -> String {
    if arguments.is_empty() {
        return name.to_owned();
    }
    let arguments = arguments
        .iter()
        .map(|argument| match argument {
            AlgebraicValueType::Parameter(name) => name.clone(),
            AlgebraicValueType::C(ty) => crate::kernel::c_type_spelling(*ty).to_owned(),
            AlgebraicValueType::Integer => "Integer".to_owned(),
            AlgebraicValueType::Algebraic { name, arguments } => {
                algebraic_type_spelling(name, arguments)
            }
        })
        .collect::<Vec<_>>();
    format!("{name}<{}>", arguments.join(", "))
}

/// `not P`, with a compound `P` parenthesized for the reader even where
/// precedence would not require it: `not (xs == ys)`.
fn negation(body: Spelled) -> Spelled {
    let text = if body.precedence == ATOM && !body.text.contains(' ') {
        body.text
    } else {
        format!("({})", body.text)
    };
    spelled(format!("not {text}"), NOT)
}

/// The place at `address`: `*p` for a plain pointer, `x` for `&x`.
fn dereference(address: Spelled) -> String {
    if address.precedence == UNARY
        && let Some(place) = address.text.strip_prefix('&')
        && !place.contains(' ')
    {
        return place.to_owned();
    }
    format!("*{}", operand(address, UNARY))
}

/// A numeric literal written in its type; a name or a compound expression
/// keeps its spelling.
fn typed_literal(text: String, suffix: &str) -> String {
    let magnitude = text.strip_prefix('-').unwrap_or(&text);
    if !magnitude.is_empty() && magnitude.chars().all(|c| c.is_ascii_digit()) {
        format!("{text}{suffix}")
    } else {
        text
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
        assert_eq!(render(&fact, &mut labels), Some("size(r) == 3".into()));
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
            assert!(render(&fact, &mut labels).is_none());
            let text = super::super::render_proposition_labeled(&fact, &mut labels);
            if depth <= 16 {
                assert!(text.contains("<unnamed A>"), "{text}");
            } else {
                assert!(text.contains('…'), "{text}");
            }
            assert!(!text.contains("no exact Click spelling"), "{text}");
            assert!(text.len() < 32 * 1024);
        }
    }

    #[test]
    fn source_facts_share_placeholder_identities_within_one_report() {
        let mut labels = SnapshotLabels::default();
        let first = equality(Bitvector32Term::Variable(Variable(998)));
        let second = equality(Bitvector32Term::Variable(Variable(999)));
        assert_eq!(source(&first, &mut labels), "<unnamed A> == 0");
        assert_eq!(source(&second, &mut labels), "<unnamed B> == 0");
        assert_eq!(source(&first, &mut labels), "<unnamed A> == 0");
        assert!(render(&first, &mut labels).is_none());
    }

    #[test]
    fn narrowed_wide_values_keep_the_signed_comparison_view() {
        let state = CState::new().with_local(
            "size",
            CValue::UInt64(Bitvector32Term::Variable(Variable(94))),
        );
        let mut labels = SnapshotLabels::with_state(ParameterBinding::default(), &state);
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
            render(&fact, &mut labels).unwrap(),
            "(int32)(uint32)size < 0"
        );
        assert_eq!(source(&fact, &mut labels), "(int32)(uint32)size < 0");
    }

    #[test]
    fn source_constants_print_in_the_type_of_their_comparison() {
        let mut labels = SnapshotLabels::default();
        labels.source_name(Variable(7), "a".into());
        labels.source_name(Variable(8), "u".into());
        labels.source_types.insert(Variable(8), CType::UInt32);
        let signed = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(7))),
                Box::new(Bitvector32Term::Constant((-56i32) as u32)),
            ),
            true,
        );
        assert_eq!(source(&signed, &mut labels), "a == -56");
        let unsigned = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(8))),
                Box::new(Bitvector32Term::Constant((-56i32) as u32)),
            ),
            false,
        );
        assert_eq!(source(&unsigned, &mut labels), "u != 4294967240u32");
        // An unsigned order over an `int32` value converts it.
        let order = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::BitwiseXor(
                    Box::new(Bitvector32Term::Variable(Variable(7))),
                    Box::new(Bitvector32Term::Constant(0x8000_0000)),
                )),
                Box::new(Bitvector32Term::Constant(1073741823 ^ 0x8000_0000)),
            ),
            true,
        );
        assert_eq!(source(&order, &mut labels), "(uint32)a <= 1073741823u32");
    }

    #[test]
    fn source_spelling_uses_minimal_parentheses_and_click_connectives() {
        let mut labels = SnapshotLabels::default();
        labels.source_name(Variable(7), "a".into());
        labels.source_name(Variable(8), "b".into());
        let a = || Box::new(Bitvector32Term::Variable(Variable(7)));
        let b = || Box::new(Bitvector32Term::Variable(Variable(8)));
        let product = Bitvector32Term::Multiply(
            Box::new(Bitvector32Term::Add(a(), b())),
            Box::new(Bitvector32Term::Subtract(a(), b())),
        );
        let less = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(Box::new(product), a()),
            false,
        );
        let masked = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::BitwiseAnd(a(), b())),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let fact = Proposition::Implies(
            Box::new(Proposition::And(Box::new(less), Box::new(masked.clone()))),
            Box::new(Proposition::Not(Box::new(masked))),
        );
        assert_eq!(
            source(&fact, &mut labels),
            "(a + b) * (a - b) >= a and (a & b) == 0 implies not ((a & b) == 0)"
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
            render(&load(before.memory(), LoadKind::Bits32), &mut labels),
            Some("at(pre, cells[0]) == 0".into())
        );
        assert_eq!(
            render(&load(after.memory(), LoadKind::Bits32), &mut labels),
            Some("cells[0] == 0".into())
        );
        assert_eq!(
            render(&load(before.memory(), LoadKind::UInt8), &mut labels),
            None
        );
        let unknown = CMemory::new().with_block("global:cells", 16);
        assert_eq!(render(&load(&unknown, LoadKind::Bits32), &mut labels), None);
        // The source policy names the unknown memory instead of refusing, so
        // the two reads of `cells[0]` stay distinct.
        assert_eq!(
            source(&load(&unknown, LoadKind::Bits32), &mut labels),
            "at(<state A>, cells[0]) == 0"
        );
        assert_eq!(
            source(&load(after.memory(), LoadKind::Bits32), &mut labels),
            "cells[0] == 0"
        );
        assert!(labels.trace_legend().contains("<state A> is "));
    }

    #[test]
    fn reassigned_parameters_do_not_rename_their_old_value_as_current() {
        let entry =
            CState::new().with_local("i", CValue::Int32(Bitvector32Term::Variable(Variable(7))));
        let current = entry
            .clone()
            .with_local("i", CValue::Int32(Bitvector32Term::Variable(Variable(8))));
        let (names, values) = crate::surface::diagnostics::local_naming_tables(&entry);
        let mut labels =
            SnapshotLabels::with_state(ParameterBinding::new(&names, &values), &current);
        assert_eq!(
            render(
                &equality(Bitvector32Term::Variable(Variable(7))),
                &mut labels
            ),
            Some("old(i) == 0".into())
        );
        assert_eq!(
            render(
                &equality(Bitvector32Term::Variable(Variable(8))),
                &mut labels
            ),
            Some("i == 0".into())
        );
    }
}
