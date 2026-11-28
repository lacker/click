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
#[cfg(test)]
use crate::kernel::CompareRelation;
use crate::kernel::OffsetView;
use crate::kernel::OverflowOperation;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::{MachineBinaryOp, MachineIntegerType, MachineUnaryOp};
use crate::kernel::{MachineCastSpelling, OldMachineTerm, cast_op, cast_term};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint32_constant, uint64_constant,
};

/// Which spelling policy a printer applies.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    /// Total source spelling for ordinary diagnostics.
    Source,
    /// Exact Click spelling, refusing unnamed operands.
    #[cfg_attr(not(test), allow(dead_code))]
    Exact,
    /// Exact spelling that also refuses every read, whose state an
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
/// `e as T`: looser than a unary operator, tighter than every binary one,
/// and left-associative, `x as int32 as uint64`.
const CAST: u8 = 15;
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

/// A machine arithmetic result must be observed before it participates in
/// a specification comparison. Otherwise `+`, `-`, and `*` are read as
/// exact Integer arithmetic and the printed comparison changes meaning.
fn comparison_operand(term: &OldMachineTerm, value: Spelled) -> Spelled {
    if matches!(
        term,
        OldMachineTerm::Binary {
            op: MachineBinaryOp::Add | MachineBinaryOp::Subtract | MachineBinaryOp::Multiply,
            ..
        }
    ) {
        atom(format!("to_integer({})", value.text))
    } else {
        value
    }
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
    fn of_type(interface_type: crate::kernel::ProgramType) -> Option<Self> {
        use crate::kernel::ProgramType;
        Some(match interface_type {
            ProgramType::Int32 => Self::Signed32,
            ProgramType::UInt32 => Self::Unsigned32,
            ProgramType::Int8 | ProgramType::Int16 => Self::Narrow { signed: true },
            ProgramType::Bool | ProgramType::UInt8 | ProgramType::UInt16 => {
                Self::Narrow { signed: false }
            }
            ProgramType::Int64 => Self::Int64,
            ProgramType::UInt64 => Self::UInt64,
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
    let target = crate::surface::diagnostics::click_cast_target(type_name);
    spelled(format!("{} as {target}", operand(value, CAST)), CAST)
}

pub(super) fn display(proposition: &Proposition, labels: &mut MemoryStateLabels) -> Option<String> {
    printer(labels, Mode::ExactIdentity)
        .proposition(proposition, 0)
        .map(|value| value.text)
        .filter(|text| text.len() <= 2048)
}

/// The total source spelling of one proposition.
pub(super) fn source(proposition: &Proposition, labels: &mut MemoryStateLabels) -> String {
    bounded(
        printer(labels, Mode::Source)
            .proposition(proposition, 0)
            .map_or_else(|| "…".into(), |value| value.text),
    )
}

pub(super) fn source_resource_fact(fact: &ResourceFact, labels: &mut MemoryStateLabels) -> String {
    bounded(printer(labels, Mode::Source).resource_fact(fact))
}

/// Whether `names` is a hidden record's schema: a resource that declares no
/// field keeps one field per field of each named child, `first.v`, and the
/// parser gives no declared field a dotted name.
pub(super) fn hidden_record_fields(names: &[&str]) -> Option<()> {
    (!names.is_empty() && names.iter().all(|name| name.contains('.'))).then_some(())
}

/// The source spelling of an instance's hidden record, `record { first.v: … }`,
/// or `None` when the instance declares its own fields.
pub(super) fn source_hidden_record(
    schema: &[(String, crate::kernel::ResourceFieldType)],
    fields: &[AlgebraicValue],
    labels: &mut MemoryStateLabels,
) -> Option<String> {
    printer(labels, Mode::Source)
        .hidden_record(schema, fields)
        .map(bounded)
}

pub(super) fn source_resource(resource: &Resource, labels: &mut MemoryStateLabels) -> String {
    bounded(printer(labels, Mode::Source).resource(resource))
}

pub(super) fn source_separation(
    left: &Resource,
    right: &Resource,
    labels: &mut MemoryStateLabels,
) -> String {
    let mut printer = printer(labels, Mode::Source);
    bounded(format!(
        "separate({}, {})",
        printer.resource_subject(left),
        printer.resource_subject(right),
    ))
}

/// The total source spelling of one C value.
pub(super) fn source_value(
    value: &crate::kernel::ProgramValue,
    labels: &mut MemoryStateLabels,
) -> String {
    bounded(
        printer(labels, Mode::Source)
            .cvalue(value, 0)
            .map_or_else(|| "…".into(), |value| value.text),
    )
}

/// The total source spelling of one exact-arithmetic term.
pub(super) fn integer(value: &IntegerTerm, labels: &mut MemoryStateLabels) -> String {
    bounded(
        printer(labels, Mode::Source)
            .integer(value, 0)
            .map_or_else(|| "…".into(), |value| value.text),
    )
}

#[cfg(test)]
pub(super) fn render(proposition: &Proposition, labels: &mut MemoryStateLabels) -> Option<String> {
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

fn printer(labels: &mut MemoryStateLabels, mode: Mode) -> Printer<'_> {
    Printer {
        labels,
        mode,
        remaining: 512,
        bound: Vec::new(),
        before_return: false,
        spelled_load_type: None,
        slice_bound: std::collections::BTreeMap::new(),
    }
}

struct Printer<'a> {
    labels: &'a mut MemoryStateLabels,
    mode: Mode,
    remaining: usize,
    /// Names of the binders in scope, innermost last.
    bound: Vec<(Variable, String)>,
    /// Whether the place being spelled is read in a memory other than the
    /// outcome state. `result` does not exist before the return, so a read
    /// there is not spelled through it.
    before_return: bool,
    /// The type the last spelled load's place states: a field's declared
    /// type, or a typed read's explicit type. A 64-bit load carries no
    /// signedness of its own, so a context of the other signedness needs a
    /// conversion only this spelling can show.
    spelled_load_type: Option<crate::kernel::ProgramType>,
    /// The element type of each bound variable that names a slice: its
    /// data pointer is spelled `s.as_ptr()`, never `s`, which is the slice
    /// (`design/rust-slice-values.md`). Binder variables are never reused,
    /// so an entry outliving its scope names nothing else.
    slice_bound: std::collections::BTreeMap<Variable, crate::kernel::SliceElement>,
}

impl Printer<'_> {
    fn source_mode(&self) -> bool {
        self.mode == Mode::Source
    }

    /// A placeholder in source mode; a refusal in the exact modes.
    fn placeholder(&mut self, text: impl FnOnce(&mut Self) -> String) -> Option<Spelled> {
        if self.source_mode() {
            self.labels.count_placeholder();
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
            .or_else(|| {
                self.labels
                    .source_name_for(variable)
                    .filter(|name| !(self.before_return && names_result(name)))
                    .map(str::to_owned)
            })
    }

    /// Spells a place read in `memory`, then qualifies it with that memory.
    fn place_read_in(
        &mut self,
        memory: &SymbolicMemory,
        place: impl FnOnce(&mut Self) -> Option<Spelled>,
    ) -> Option<Spelled> {
        let outer = self.before_return;
        self.before_return = outer
            || !matches!(
                self.labels.source_memory_context(memory),
                Some(("current", _))
            );
        let place = place(self);
        self.before_return = outer;
        self.qualify(memory, place?)
    }

    /// A name for a bound variable, `k`, `k1`, ..., that no other bound
    /// variable or free source name uses: a free `k` stays `k`, and the
    /// binder is renamed rather than capturing it.
    /// The binder's written name, unless another binder in scope or a named
    /// free variable already spells it; then a fresh name as [`Self::binder`]
    /// chooses one, so the printed proposition never captures.
    fn written_binder(&mut self, variable: Variable, written: Option<&str>) -> String {
        match written {
            Some(name)
                if !self.bound.iter().any(|(_, bound)| bound == name)
                    && !self.labels.names_a_variable(name) =>
            {
                self.bound.push((variable, name.to_owned()));
                name.to_owned()
            }
            _ => self.binder(variable),
        }
    }

    fn binder(&mut self, variable: Variable) -> String {
        let mut index = self.bound.len();
        let name = loop {
            let name = if index == 0 {
                "k".to_string()
            } else {
                format!("k{index}")
            };
            if !self.bound.iter().any(|(_, bound)| *bound == name)
                && !self.labels.names_a_variable(&name)
            {
                break name;
            }
            index += 1;
        };
        self.bound.push((variable, name.clone()));
        name
    }

    /// A match arm's pattern, `Up(u)`, binding each field the arm's body
    /// reads by its written name, or a fresh one where that would capture;
    /// the caller pops the returned count of binders
    /// once it has spelled the body. A field that is not a variable is `_`.
    fn arm_pattern(
        &mut self,
        variant: &str,
        bindings: &[crate::kernel::AlgebraicValue],
        names: &crate::kernel::BindingNames,
    ) -> (String, usize) {
        use crate::kernel::AlgebraicValue as V;
        if bindings.is_empty() {
            if crate::surface::tuples::arity(variant).is_some() {
                return ("()".to_owned(), 0);
            }
            return (variant.to_owned(), 0);
        }
        let mut spelled = Vec::with_capacity(bindings.len());
        let mut bound = 0;
        for (index, binding) in bindings.iter().enumerate() {
            let variable = match binding {
                // A slice binder names the slice, its thin part and its
                // count (`design/rust-slice-values.md`, step 2b-iii-b-i).
                V::Program(crate::kernel::ProgramValue::Pointer(pointer))
                    if pointer.is_wide()
                        && matches!(pointer.address().offset.view(), OffsetView::Constant(0)) =>
                {
                    match (&pointer.address().base, pointer.program_type()) {
                        (
                            crate::kernel::AddressBase::Symbolic(variable),
                            crate::kernel::ProgramType::SlicePointer(element),
                        ) => {
                            self.slice_bound.insert(*variable, element);
                            Some(*variable)
                        }
                        _ => None,
                    }
                }
                V::Program(value) => match value.numeric_value() {
                    crate::kernel::ProgramValue::Parameter(term) => match term.node {
                        AlgebraicTermNode::Variable(variable) => Some(variable),
                        _ => None,
                    },
                    crate::kernel::arithmetic_c_value!(OldMachineTerm::Variable(variable)) => {
                        Some(*variable)
                    }
                    _ => None,
                },
                V::Integer(IntegerTerm::Variable(variable)) => Some(*variable),
                V::Algebraic(term) => match term.node {
                    AlgebraicTermNode::Variable(variable) => Some(variable),
                    _ => None,
                },
                V::Integer(_) => None,
            };
            match variable {
                Some(variable) => {
                    spelled.push(self.written_binder(variable, names.get(index)));
                    bound += 1;
                }
                None => spelled.push("_".to_owned()),
            }
        }
        if crate::surface::tuples::arity(variant).is_some() {
            return (crate::surface::tuples::spell(&spelled), bound);
        }
        (format!("{variant}({})", spelled.join(", ")), bound)
    }

    fn proposition(&mut self, proposition: &Proposition, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        match proposition {
            // Completed access evidence is kernel bookkeeping. Its observed
            // value has the public source-region spelling read_event(i).result.
            Proposition::VolatileAccess(_) => None,
            Proposition::ConditionIs(condition, polarity) => {
                self.condition(condition.old_form(), *polarity, depth)
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
            Proposition::SequenceMembership { element, sequence } => {
                let element = self.cvalue(element.old_form(), depth)?;
                let sequence = self.sequence(sequence, depth)?;
                Some(atom(format!(
                    "{} in {}",
                    operand(element, SHIFT),
                    sequence.text
                )))
            }
            _ if !self.source_mode() => None,
            Proposition::Predicate { name, arguments } => {
                if let Some(surface) =
                    crate::surface::proof::program_termination::predicate_spelling(name)
                {
                    return Some(atom(crate::surface::printing::source_click_proposition(
                        &surface,
                    )));
                }
                // Type evidence about a pointer is written `is_a<T>(p)`.
                if let (Some(spelling), [pointer]) = (
                    crate::kernel::object_type_predicate_spelling(name),
                    arguments.as_slice(),
                ) {
                    let pointer = self.term(pointer, depth)?;
                    return Some(atom(format!("is_a<{spelling}>({})", pointer.text)));
                }
                if name == &format!("{}1", crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX)
                    && let [origin, start, end] = arguments.as_slice()
                {
                    if !self.source_mode() {
                        return None;
                    }
                    // Diagnostic notation for the existing opaque-domain fact:
                    // the origin is essential; address equality is insufficient.
                    let origin = self.term(origin, depth)?;
                    let start = self.term(start, depth)?;
                    let end = self.term(end, depth)?;
                    return Some(atom(format!(
                        "subobject bounds of {} cover bytes [{}, {})",
                        origin.text, start.text, end.text,
                    )));
                }
                // Bookkeeping predicates have no Click spelling; their kernel
                // name is the most honest rendering.
                let surface = crate::kernel::predicate_source_name(name).unwrap_or(name);
                let mut spelled_arguments = Vec::new();
                let mut arguments = arguments.iter();
                while let Some(argument) = arguments.next() {
                    let spelled = match argument {
                        // The logical resource-state argument is implicit.
                        Term::ExecutionState(_) => continue,
                        // Each array argument is a (memory, pointer) pair.
                        // Its state is part of the argument's identity.
                        Term::ArrayReadPoint(memory) => {
                            let pointer @ term_source_0 @ Term::ProgramValue(_) =
                                arguments.next()?
                            else {
                                return None;
                            };
                            let (Some(crate::kernel::ProgramValue::Pointer(_)),) =
                                (term_source_0.program_value_native(),)
                            else {
                                return None;
                            };
                            self.place_read_in(memory.memory(), |printer| {
                                printer.term(pointer, depth)
                            })?
                        }
                        _ => self.term(argument, depth)?,
                    };
                    spelled_arguments.push(spelled.text);
                }
                Some(atom(format!("{surface}({})", spelled_arguments.join(", "))))
            }
            Proposition::ForAll {
                var,
                sort,
                body,
                name,
            } => {
                if let Some(crate::kernel::ProgramType::SlicePointer(element)) = sort.pointer_type()
                {
                    self.slice_bound.insert(**var, element);
                }
                let sort = self.sort(sort);
                let name = self.written_binder(**var, name.as_str());
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
                if let Some(crate::kernel::ProgramType::SlicePointer(element)) = sort.pointer_type()
                {
                    self.slice_bound.insert(**var, element);
                }
                let sort = self.sort(sort);
                let binder = if name.is_empty() {
                    self.binder(**var)
                } else {
                    self.bound.push((**var, name.clone()));
                    name.clone()
                };
                let body = self.proposition(body, depth);
                self.bound.pop();
                Some(atom(format!(
                    "exists ({binder}: {sort}) {{ {} }}",
                    body?.text
                )))
            }
            // Viewability is about an object's size and lifetime, and a
            // lifetime can end between two points, so a fact checked in an
            // earlier memory keeps its point: `at(point, viewable(..))`, as a
            // proof writes it to carry the fact forward.
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide,
                ..
            } => {
                let fact = atom(format!(
                    "viewable({})",
                    self.byte_range(base, bytes.old_form(), *wide, depth)
                ));
                self.qualify_fact(memory, fact)
            }
            Proposition::MemoryCanStore {
                pointer,
                byte_width,
                ..
            } => {
                let place = self.place_at(pointer, depth);
                Some(atom(format!("<{place} is writable ({byte_width} bytes)>")))
            }
            Proposition::MemoryReadDefined {
                at: Some(id),
                pointer,
                ..
            } => {
                let (point, naming) = self.labels.definedness_point_context(*id);
                let Some(point) = point else {
                    return Some(atom(format!("defined({})", self.place_at(pointer, depth))));
                };
                let place = naming
                    .as_deref()
                    .and_then(|(parameters, arguments)| {
                        crate::surface::diagnostics::diagnostic_source_cell(
                            pointer,
                            ParameterBinding::new(parameters, arguments),
                        )
                    })
                    .or_else(|| {
                        if !self.source_mode() {
                            return None;
                        }
                        if let Some(place) = naming.as_deref().and_then(|tables| {
                            self.parameter_relative_pointer(pointer, depth, tables)
                        }) {
                            return Some(dereference(place));
                        }
                        Some(format!("*{}", self.labels.placeholder_pointer(pointer)))
                    })?;
                Some(atom(format!("at({point}, defined({place}))")))
            }
            Proposition::MemoryReadDefined {
                memory, pointer, ..
            } => {
                let place = self.place_read_in(memory, |printer| {
                    Some(atom(printer.place_at(pointer, depth)))
                })?;
                Some(atom(format!("defined({})", place.text)))
            }
            Proposition::MemoryLoads { pointer, .. } => {
                let place = self.place_at(pointer, depth);
                Some(atom(format!("<the read of {place}>")))
            }
            Proposition::ResourceSeparate { left, right } => Some(atom(format!(
                "separate({}, {})",
                self.resource(left),
                self.resource(right)
            ))),
            Proposition::ResourceViewable {
                memory, resource, ..
            } => {
                let fact = atom(format!("viewable({})", self.resource(resource)));
                self.qualify_fact(memory, fact)
            }
            Proposition::ResourceContains { parent, child } => Some(atom(format!(
                "contains({}, {})",
                self.resource(parent),
                self.resource(child)
            ))),
            Proposition::ResourceComposition(context) => {
                const LIMIT: usize = 8;
                let (count, entries) = context.diagnostic_facts(LIMIT);
                let mut held = entries
                    .map(|fact| self.resource_fact(fact))
                    .collect::<Vec<_>>();
                if count > LIMIT {
                    held.push(format!("… {} more", count - LIMIT));
                }
                Some(atom(format!("<held together: {}>", held.join(", "))))
            }
            Proposition::MemoryMutatesOnly {
                before,
                after,
                writes,
                ..
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
            Proposition::MemoryEffectSummary {
                before,
                after,
                mutable_ranges,
                ..
            } => {
                let before = self.state_phrase(before);
                let after = self.state_phrase(after);
                Some(atom(format!(
                    "<{} written range(s) between {before} and {after}>",
                    mutable_ranges.len()
                )))
            }
            Proposition::HeapAllocationFreed {
                before,
                after,
                blocks,
                ..
            } => {
                let bases = blocks
                    .iter()
                    .map(|(base, _)| self.pointer(base, depth).map(|base| base.text))
                    .collect::<Option<Vec<_>>>()?
                    .join(", ");
                let before = self.state_phrase(before);
                let after = self.state_phrase(after);
                Some(atom(format!(
                    "<{bases} freed between {before} and {after}>"
                )))
            }
            Proposition::ProgramExpressionEvaluates { .. }
            | Proposition::ProgramConditionEvaluates { .. }
            | Proposition::ProgramStatementVerifies { .. }
            | Proposition::ProgramFunctionVerifies { .. } => {
                Some(atom("<a fact about executing C code>"))
            }
            Proposition::ProgramFunctionPartiallySatisfiesSpecification { .. } => {
                Some(atom("<a function satisfies its specification>"))
            }
        }
    }

    fn sort(&self, sort: &Sort) -> String {
        match sort {
            Sort::Condition => "bool".into(),
            Sort::Bitvector32 | Sort::ProgramInt32 => "int32".into(),
            Sort::ProgramInt64 => "int64".into(),
            Sort::Integer => "Integer".into(),
            Sort::ProgramInteger(ty) => machine_type_spelling(*ty).into(),
            Sort::ProgramObjectPointer(_, class) => format!("{}*", class.spelling()),
            Sort::ProgramPointer(ty) => crate::kernel::program_type_spelling(*ty).into(),
            Sort::Algebraic(ty) => algebraic_type_spelling(&ty.name, &ty.arguments),
        }
    }

    /// A state's role in a sentence: `function entry`, `here`, a recorded
    /// point, or a report-local `<state A>`.
    fn state_phrase(&mut self, memory: &SymbolicMemory) -> String {
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
        condition: &OldConditionTerm,
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
            OldConditionTerm::Constant(value) => {
                return Some(atom((value == &polarity).to_string()));
            }
            OldConditionTerm::Variable(variable) => {
                let name = match self.variable_name(*variable) {
                    Some(name) => name,
                    None if self.source_mode() => self.unnamed_variable(*variable),
                    None => return None,
                };
                return Some(negate(name, polarity));
            }
            OldConditionTerm::PointerEqual(left, right) => {
                if self.source_mode()
                    && !left.is_wide()
                    && !right.is_wide()
                    && distinct_pointers_at_one_address(left, right)
                {
                    if let Some(naming) = &self.labels.naming
                        && let (Some(left), Some(right)) = (
                            self.exact_pointer_value(left, naming),
                            self.exact_pointer_value(right, naming),
                        )
                    {
                        let operator = if polarity { "==" } else { "!=" };
                        return Some(atom(format!("{left} {operator} {right}")));
                    }
                    self.labels.count_placeholder();
                    let address = self.pointer(left.address(), depth)?;
                    return Some(atom(describe_pointer_comparison(&address.text, polarity)));
                }
                let left = self.cvalue(
                    &crate::kernel::ProgramValue::Pointer((**left).clone()),
                    depth,
                )?;
                let right = self.cvalue(
                    &crate::kernel::ProgramValue::Pointer((**right).clone()),
                    depth,
                )?;
                return Some(atom(format!(
                    "{} {} {}",
                    operand(left, SHIFT),
                    if polarity { "==" } else { "!=" },
                    operand(right, SHIFT)
                )));
            }
            OldConditionTerm::AddressEqual(left, right) => {
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
                    if left != right && **left != Address::null() && **right != Address::null() {
                        return None;
                    }
                    let pointer = |p: &Address, labels: &MemoryStateLabels| {
                        if p == &Address::null() {
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
                let address_only = **left != Address::null() && **right != Address::null();
                let left = self.pointer(left, depth)?;
                let right = self.pointer(right, depth)?;
                return Some(atom(format!(
                    "{} {} {}",
                    if address_only {
                        format!("address({})", left.text)
                    } else {
                        operand(left, SHIFT)
                    },
                    if polarity { "==" } else { "!=" },
                    if address_only {
                        format!("address({})", right.text)
                    } else {
                        operand(right, SHIFT)
                    }
                )));
            }
            OldConditionTerm::AddressOffsetEqual(left, right) => {
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
            OldConditionTerm::AlgebraicEqual(left, right) => {
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
                    OldConditionTerm::IntegerEqual(..) => "==",
                    OldConditionTerm::IntegerNotEqual(..) => "!=",
                    OldConditionTerm::IntegerLessThan(..) => "<",
                    OldConditionTerm::IntegerLessEqual(..) => "<=",
                    OldConditionTerm::IntegerGreaterThan(..) => ">",
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
            OldConditionTerm::Float32(float) | OldConditionTerm::Float64(float) => {
                if !self.source_mode() {
                    return None;
                }
                let single = matches!(condition, OldConditionTerm::Float32(_));
                return match float {
                    crate::kernel::FloatCondition::Comparison {
                        operator,
                        left,
                        right,
                    } => {
                        use crate::kernel::ComparisonOperator as C;
                        let symbol = match operator {
                            C::Equal => "==",
                            C::NotEqual => "!=",
                            C::LessThan => "<",
                            C::LessEqual => "<=",
                            C::GreaterThan => ">",
                            C::GreaterEqual => ">=",
                        };
                        let left = self.float_operand(left, single, depth)?;
                        let right = self.float_operand(right, single, depth)?;
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
                    crate::kernel::FloatCondition::Classification {
                        classification,
                        value,
                    } => {
                        let value = self.float_operand(value, single, depth)?;
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
            // The `Bool` value forms (`design/machine-integers.md`, Stage 5)
            // in their Surface spellings: an application `f(x)`, a
            // conditional `if c { a } else { b }`, an equality `a == b`, a
            // read the place it reads.
            OldConditionTerm::BoolApplication(application) => {
                let call = self.call(application.name(), application.arguments(), depth)?;
                return Some(if polarity { call } else { negation(call) });
            }
            // A negation, `if c { false } else { true }`, is `not c`: an
            // integer converted to `Bool` prints `x != 0`.
            OldConditionTerm::BoolIf { .. } if condition.bool_negation_operand().is_some() => {
                let operand = condition.bool_negation_operand()?;
                return self.condition(operand, !polarity, depth);
            }
            OldConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => {
                let condition = self.condition(condition, true, depth)?;
                let then_condition = self.condition(then_condition, true, depth)?;
                let else_condition = self.condition(else_condition, true, depth)?;
                let spelled_if = atom(format!(
                    "if {} {{ {} }} else {{ {} }}",
                    condition.text, then_condition.text, else_condition.text
                ));
                return Some(if polarity {
                    spelled_if
                } else {
                    negation(spelled_if)
                });
            }
            OldConditionTerm::BoolEqual(left, right) => {
                let left = self.condition(left, true, depth)?;
                let right = self.condition(right, true, depth)?;
                return Some(atom(format!(
                    "{} {} {}",
                    operand(left, ATOM),
                    if polarity { "==" } else { "!=" },
                    operand(right, ATOM)
                )));
            }
            _ => {}
        }
        let (operator, left, right) = condition.as_bitvector_comparison()?;
        let symbol = operator.program_symbol();
        if operator.is_overflow() {
            return self.overflow(condition, operator, left, right, polarity, depth);
        }
        let operator_text = comparison(symbol, polarity);
        let operand_type = operator.operand_type();
        let is_equality = symbol == "==";
        // A `uint32` order spells its operands as `uint32` values.
        if operand_type == "uint32" && !is_equality {
            if !self.source_mode() {
                return Some(atom(format!(
                    "{} {operator_text} {} (unsigned)",
                    self.exact_operand(left, Some(false), depth)?,
                    self.exact_operand(right, Some(false), depth)?
                )));
            }
            let left = comparison_operand(left, self.as_type(left, Hint::Unsigned32, depth)?);
            let right = comparison_operand(right, self.as_type(right, Hint::Unsigned32, depth)?);
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
            let signed = if is_equality && operand_type == "uint32" {
                Some(false)
            } else if is_equality {
                [left, right].iter().find_map(|term| {
                    let OldMachineTerm::Variable(variable) = term else {
                        return None;
                    };
                    match self.labels.source_types.get(variable) {
                        Some(crate::kernel::ProgramType::Int32) => Some(true),
                        Some(crate::kernel::ProgramType::UInt32) => Some(false),
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
        let (left_spelling, right_spelling) = match operand_type {
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
                let hint = match operand_type {
                    "int32" => hint.or(Some(Hint::Signed32)),
                    // A `uint32` equality reads its operands as `uint32`
                    // (rule K6).
                    "uint32" => hint.or(Some(Hint::Unsigned32)),
                    _ => hint,
                };
                (
                    self.bitvector(left, hint, depth)?,
                    self.bitvector(right, hint, depth)?,
                )
            }
        };
        Some(atom(format!(
            "{} {operator_text} {}",
            operand(comparison_operand(left, left_spelling), SHIFT),
            operand(comparison_operand(right, right_spelling), SHIFT)
        )))
    }

    /// An overflow test is the negation of `defined(a op b)`; a constant
    /// right operand reads as the bound it puts on the left one.
    fn overflow(
        &mut self,
        condition: &OldConditionTerm,
        operator: crate::kernel::BitvectorComparisonOp,
        a: &OldMachineTerm,
        b: &OldMachineTerm,
        polarity: bool,
        depth: usize,
    ) -> Option<Spelled> {
        if let (
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                ..
            }
            | OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Subtract,
                ..
            },
            int32_constant!(bits),
        ) = (condition, b)
        {
            let offset = constant_u32(*bits) as i32 as i64;
            if offset == 0 {
                return Some(atom((!polarity).to_string()));
            }
            let addition = matches!(
                condition,
                OldConditionTerm::Overflows {
                    format: MachineIntegerType::Int32,
                    op: OverflowOperation::Add,
                    ..
                }
            );
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
        let precedence = match operator.program_symbol() {
            "+" | "-" => ADD,
            "<<" => SHIFT,
            _ => MULTIPLY,
        };
        let left = self.bitvector(a, Some(hint), depth)?;
        let right = self.bitvector(b, Some(hint), depth)?;
        let operation = format!(
            "{} {} {}",
            operand(left, precedence),
            operator.program_symbol(),
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
        value: &OldMachineTerm,
        signed: Option<bool>,
        depth: usize,
    ) -> Option<String> {
        if signed == Some(true) && matches!(value, cast_term!(UInt32From64, _)) {
            let value = self.bitvector(value, None, depth)?;
            return Some(cast("int32", value).text);
        }
        if let uint32_constant!(value) = value {
            return Some(constant_u32(*value).to_string());
        }
        if let bits32_constant!(value) = value {
            return match signed {
                Some(true) => Some((constant_u32(*value) as i32).to_string()),
                Some(false) => Some(constant_u32(*value).to_string()),
                None if constant_u32(*value) <= i32::MAX as u32 => {
                    Some(constant_u32(*value).to_string())
                }
                None => None,
            };
        }
        self.bitvector(value, None, depth)
            .map(|spelling| operand(comparison_operand(value, spelling), SHIFT))
    }

    /// `value` read as `hint`: a constant written in that type and any
    /// other operand of another known type converted with a cast.
    fn as_type(&mut self, value: &OldMachineTerm, hint: Hint, depth: usize) -> Option<Spelled> {
        let literal = matches!(
            value,
            bits32_constant!(_) | int64_constant!(_) | uint64_constant!(_)
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
        // plain: `(x + 1) as uint32`.
        let inner_hint = if hint == Hint::Unsigned32 && own.is_none() && !literal {
            None
        } else {
            Some(hint)
        };
        let spelled_value = match value {
            // A constant in a 64-bit comparison is written in that type.
            int64_constant!(bits) if hint == Hint::UInt64 => {
                atom(format!("{}u64", constant_i64(*bits) as u64))
            }
            uint64_constant!(bits) if hint == Hint::Int64 => {
                atom(format!("{}i64", constant_u64(*bits) as i64))
            }
            _ => self.operand_as(value, inner_hint, depth)?,
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

    /// `value` spelled as an operand read as `hint`. A 64-bit load is
    /// signless, so the type its place states decides whether the operand
    /// shows a conversion: a `size_t` field in an `int64` sum is
    /// `(b->offset as int64) + 1i64`.
    fn operand_as(
        &mut self,
        value: &OldMachineTerm,
        hint: Option<Hint>,
        depth: usize,
    ) -> Option<Spelled> {
        self.spelled_load_type = None;
        let spelled_value = self.bitvector(value, hint, depth)?;
        let wanted = match hint {
            Some(Hint::Int64) => "int64",
            Some(Hint::UInt64) => "uint64",
            _ => return Some(spelled_value),
        };
        let converted = matches!(
            value,
            OldMachineTerm::MemoryLoad(_, _, crate::kernel::LoadKind::Bits64)
        ) && self
            .spelled_load_type
            .and_then(Hint::of_type)
            .is_some_and(|spelled| Some(spelled) != hint);
        Some(if converted {
            cast(wanted, spelled_value)
        } else {
            spelled_value
        })
    }

    /// The source type of a term, where it shows.
    fn hint_of(&self, value: &OldMachineTerm) -> Option<Hint> {
        use OldMachineTerm as B;
        match value {
            int64_constant!(_) => Some(Hint::Int64),
            uint64_constant!(_) => Some(Hint::UInt64),
            uint32_constant!(_) => Some(Hint::Unsigned32),
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
            cast_term!(Int64From32, _) | cast_term!(Int64FromUInt32, _) => Some(Hint::Int64),
            cast_term!(UInt64From32, _)
            | cast_term!(UInt64FromInt32, _)
            | cast_term!(UInt64FromInt64, _) => Some(Hint::UInt64),
            cast_term!(UInt32From64, _) => Some(Hint::Unsigned32),
            B::Cast {
                spelling: MachineCastSpelling::Generic,
                to: destination,
                ..
            }
            | B::IntegerToMachine { destination, .. } => Hint::of_machine(*destination),
            B::If {
                then_term,
                else_term,
                ..
            } => self.hint_of(then_term).or_else(|| self.hint_of(else_term)),
            B::Unary {
                format: MachineIntegerType::Int64,
                op: MachineUnaryOp::BitwiseNot,
                operand: _,
            } => Some(Hint::Int64),
            B::Unary {
                format: MachineIntegerType::UInt64,
                op: MachineUnaryOp::BitwiseNot,
                operand: _,
            } => Some(Hint::UInt64),
            unary_term!(Int32, BitwiseNot, inner) => self.hint_of(inner),
            _ => {
                let (operator, left, right) = value.as_binary()?;
                use crate::kernel::BitvectorBinaryOp as Op;
                match operator {
                    Op::Machine(
                        MachineIntegerType::Int64,
                        MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::Multiply
                        | MachineBinaryOp::Divide
                        | MachineBinaryOp::Remainder
                        | MachineBinaryOp::ShiftLeft
                        | MachineBinaryOp::ShiftRight
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr
                        | MachineBinaryOp::BitwiseXor,
                    ) => Some(Hint::Int64),
                    Op::Machine(
                        MachineIntegerType::UInt64,
                        MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::Multiply
                        | MachineBinaryOp::Divide
                        | MachineBinaryOp::Remainder
                        | MachineBinaryOp::ShiftLeft
                        | MachineBinaryOp::ShiftRight
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr
                        | MachineBinaryOp::BitwiseXor,
                    ) => Some(Hint::UInt64),
                    Op::Machine(
                        crate::kernel::MachineIntegerType::UInt32,
                        crate::kernel::MachineBinaryOp::Divide,
                    )
                    | Op::Machine(
                        crate::kernel::MachineIntegerType::UInt32,
                        crate::kernel::MachineBinaryOp::Remainder,
                    )
                    | Op::Machine(
                        crate::kernel::MachineIntegerType::UInt32,
                        crate::kernel::MachineBinaryOp::ShiftRight,
                    ) => Some(Hint::Unsigned32),
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
            Term::Bitvector32(value) => self.bitvector(value.old_form(), None, depth + 1),
            Term::Integer(value) => self.integer(value.old_form(), depth + 1),
            term_source_0 @ Term::Condition(_)
                if let Some(OldConditionTerm::Constant(value)) = term_source_0.old_condition() =>
            {
                Some(atom(value.to_string()))
            }
            Term::ProgramValue(value) => self.cvalue(value.old_form(), depth + 1),
            Term::Algebraic(value) => self.algebraic(value.old_form(), depth + 1),
            Term::Sequence(value) => self.sequence(value, depth + 1),
            _ if !self.source_mode() => None,
            Term::Condition(condition) => self.condition(condition.old_form(), true, depth + 1),
            Term::PointerOffset(offset) => Some(atom(self.offset(offset.old_form(), depth + 1))),
            Term::ArrayReadPoint(point) => Some(atom(self.state_phrase(point.memory()))),
            Term::ExecutionState(state) => Some(atom(self.state_phrase(state.memory()))),
        }
    }

    fn sequence(
        &mut self,
        sequence: &crate::kernel::SequenceTerm,
        depth: usize,
    ) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        use crate::kernel::SequenceTermNode;
        match sequence.node.as_ref() {
            SequenceTermNode::Literal(values) => {
                let mut elements = Vec::new();
                for value in values.iter() {
                    if self.remaining == 0 {
                        if !self.source_mode() {
                            return None;
                        }
                        elements.push("…".into());
                        break;
                    }
                    elements.push(self.cvalue(value, depth + 1)?.text);
                }
                Some(atom(format!("[{}]", elements.join(", "))))
            }
            SequenceTermNode::Concat(left, right) => Some(spelled(
                format!(
                    "{} ++ {}",
                    operand(self.sequence(left, depth + 1)?, ADD),
                    operand(self.sequence(right, depth + 1)?, ADD + 1)
                ),
                ADD,
            )),
        }
    }

    fn offset(&mut self, offset: &AddressOffset, depth: usize) -> String {
        match offset.view() {
            OffsetView::Constant(bytes) => bytes.to_string(),
            OffsetView::Variable(variable) => self
                .variable_name(variable)
                .unwrap_or_else(|| self.unnamed_variable(variable)),
            OffsetView::Add(left, right) => format!(
                "{} + {}",
                self.offset(left, depth + 1),
                self.offset(right, depth + 1)
            ),
            OffsetView::Int32Scaled { index, byte_width }
            | OffsetView::Int64Scaled {
                index, byte_width, ..
            } => {
                let value = self
                    .bitvector(index.structural_value(), None, depth + 1)
                    .map_or_else(|| "…".into(), |value| operand(value, MULTIPLY));
                if byte_width == 1 {
                    value
                } else {
                    format!("{value} * {byte_width}")
                }
            }
        }
    }

    /// Keep the float type and exact bits in every literal operand.
    fn float_operand(
        &mut self,
        value: &OldMachineTerm,
        single: bool,
        depth: usize,
    ) -> Option<Spelled> {
        if !matches!(value, OldMachineTerm::Constant { .. }) {
            return self.bitvector(value, None, depth);
        }
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let value = if single {
            crate::kernel::ProgramValue::Float32(value.clone())
        } else {
            crate::kernel::ProgramValue::Float64(value.clone())
        };
        crate::surface::diagnostics::exact_float_literal_spelling(&value).map(atom)
    }

    fn bitvector(
        &mut self,
        value: &OldMachineTerm,
        hint: Option<Hint>,
        depth: usize,
    ) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        use OldMachineTerm as B;
        match value {
            int32_constant!(value) => return self.constant(constant_u32(*value), hint),
            // A `uint32` constant is written in its own type.
            uint32_constant!(value) => {
                return self.constant(constant_u32(*value), Some(Hint::Unsigned32));
            }
            int64_constant!(value) => {
                return Some(atom(format!("{value}i64", value = constant_i64(*value))));
            }
            uint64_constant!(value) => {
                return Some(atom(format!("{value}u64", value = constant_u64(*value))));
            }
            B::Variable(variable) if variable.counted_slice().is_some() => {
                return self.slice_count(value, depth);
            }
            B::PureApplicationCount(_) => return self.slice_count(value, depth),
            B::MemoryLoad(_, _, crate::kernel::LoadKind::SliceCount) => {
                return self.slice_count(value, depth);
            }
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
                if let Some(field) =
                    crate::kernel::model_fields::entry_model_field_surface(*variable)
                {
                    return Some(atom(field));
                }
                if crate::kernel::model_fields::registered_model_field_origin(*variable).is_some() {
                    return self.placeholder(|printer| printer.unnamed_variable(*variable));
                }
                if let Some(field) = crate::kernel::model_fields::model_field_surface(*variable) {
                    return Some(atom(field));
                }
                if let Some(count) =
                    crate::kernel::model_fields::registered_population_entry_count(*variable)
                    && let Some(member) = &count.member
                {
                    let member = self.resource_arguments(&count.family, member);
                    return Some(atom(format!("old(count({member}))")));
                }
                if let Some(count) =
                    crate::kernel::model_fields::registered_population_entry_count(*variable)
                    && let Some(anchor) = self.pointer(&count.anchor, depth + 1)
                {
                    let wildcards = ", _".repeat(count.wildcards);
                    return Some(atom(format!(
                        "old(count({}({}{wildcards})))",
                        count.family, anchor.text
                    )));
                }
                return self.placeholder(|printer| printer.unnamed_variable(*variable));
            }
            B::MemoryLoad(memory, pointer, kind) => {
                if self.source_mode()
                    && let Some(name) = self.labels.source_read_name_for(value)
                {
                    return Some(atom(name.to_string()));
                }
                return self.load(memory.shared_memory().as_ref(), pointer, *kind, depth);
            }
            cast_term!(UInt32From64, inner) if !self.source_mode() => {
                let inner = self.bitvector(inner, None, depth)?;
                return Some(cast("uint32", inner));
            }
            _ => {}
        }
        if let Some((operator, left, right)) = value.as_binary() {
            if !self.source_mode()
                && !matches!(
                    value,
                    binary_term!(Int32, Add, ..)
                        | binary_term!(Int32, Subtract, ..)
                        | binary_term!(Int32, Multiply, ..)
                        | B::Binary {
                            format: MachineIntegerType::UInt64,
                            op: MachineBinaryOp::Add
                                | MachineBinaryOp::Subtract
                                | MachineBinaryOp::Multiply
                                | MachineBinaryOp::Divide
                                | MachineBinaryOp::Remainder,
                            ..
                        }
                )
            {
                return None;
            }
            let symbol = operator.program_symbol();
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
            let (left, right) = match operator {
                crate::kernel::BitvectorBinaryOp::Float32(_) => (
                    self.float_operand(left, true, depth)?,
                    self.float_operand(right, true, depth)?,
                ),
                crate::kernel::BitvectorBinaryOp::Float64(_) => (
                    self.float_operand(left, false, depth)?,
                    self.float_operand(right, false, depth)?,
                ),
                _ => (
                    self.operand_as(left, operand_hint, depth)?,
                    self.operand_as(right, right_hint, depth)?,
                ),
            };
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
                U::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineUnaryOp::BitwiseNot,
                )
                | U::Machine(_, MachineUnaryOp::BitwiseNot) => (Some("~"), None),
                U::Float32Negate | U::Float64Negate => (Some("-"), None),
                cast_op!(Int64From32) | cast_op!(Int64FromUInt32) => (None, Some("int64")),
                cast_op!(UInt64From32) | cast_op!(UInt64FromInt32) | cast_op!(UInt64FromInt64) => {
                    (None, Some("uint64"))
                }
                cast_op!(UInt32From64) => (None, Some("uint32")),
                U::Cast {
                    spelling: MachineCastSpelling::Generic,
                    to: destination,
                    ..
                } => (None, Some(machine_type_spelling(destination))),
            };
            let inner_hint = match operator {
                U::Machine(
                    crate::kernel::MachineIntegerType::Int32,
                    crate::kernel::MachineUnaryOp::BitwiseNot,
                )
                | U::Machine(_, MachineUnaryOp::BitwiseNot) => hint,
                cast_op!(Int64FromUInt32) | cast_op!(UInt64From32) => Some(Hint::Unsigned32),
                cast_op!(Int64From32) | cast_op!(UInt64FromInt32) => Some(Hint::Signed32),
                cast_op!(UInt64FromInt64) => Some(Hint::Int64),
                U::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: source,
                    ..
                } => Hint::of_machine(source),
                _ => None,
            };
            let inner = match operator {
                U::Float32Negate => self.float_operand(inner, true, depth)?,
                U::Float64Negate => self.float_operand(inner, false, depth)?,
                _ => self.bitvector(inner, inner_hint, depth)?,
            };
            return Some(match (prefix, type_name) {
                (Some(prefix), _) => spelled(format!("{prefix}{}", operand(inner, UNARY)), UNARY),
                (None, Some(name)) => cast(name, inner),
                (None, None) => inner,
            });
        }
        match value {
            // An 8- or 16-bit constant reads as its value, as the 32-bit
            // carrier of a narrow value did; its type, where printed, comes
            // from the value it is (`typed`).
            crate::kernel::native_constant!(format, bits) if format.format().bits() < 32 => {
                Some(atom(
                    crate::kernel::MachineIntegerConstant::from_term_bits(format.format(), *bits)
                        .to_integer()
                        .to_string(),
                ))
            }
            crate::kernel::native_constant!(format, bits) => Some(atom(format!(
                "{}{}128",
                crate::kernel::MachineIntegerConstant::from_term_bits(format.format(), *bits)
                    .to_integer(),
                if format.format().is_signed() {
                    "i"
                } else {
                    "u"
                }
            ))),
            // Rule C1. A specification `Bool` travels as its cast to
            // `uint8`, which reads as the `Bool` itself; any other format is
            // the written cast `b as F`.
            B::BoolCast { to, value } => {
                let condition = self.condition(value, true, depth)?;
                if *to == crate::kernel::MachineIntegerType::UInt8 {
                    Some(condition)
                } else {
                    // A cast of a comparison, `(x != 0) as int32`, keeps the
                    // comparison together.
                    let condition = if matches!(
                        value.as_ref(),
                        OldConditionTerm::Variable(_)
                            | OldConditionTerm::Constant(_)
                            | OldConditionTerm::BoolApplication(_)
                    ) {
                        condition
                    } else {
                        atom(format!("({})", condition.text))
                    };
                    Some(cast(machine_type_spelling(*to), condition))
                }
            }
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
            B::PureFunctionApplication { name, arguments }
                if name == "c_float32_to_float64" && arguments.len() == 1 =>
            {
                Some(cast(
                    "double",
                    self.float_operand(&arguments[0], true, depth)?,
                ))
            }
            B::PureFunctionApplication { name, arguments }
                if let Some(spelled) =
                    crate::kernel::layout_term_spelling(name, arguments.len()) =>
            {
                Some(atom(crate::languages::display_source_names(&spelled)))
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
                    let (pattern, bound) =
                        self.arm_pattern(&arm.variant, &arm.bindings, &arm.binding_names);
                    let body = self.bitvector(&arm.body, hint, depth);
                    self.bound.truncate(self.bound.len() - bound);
                    spelled_arms.push(format!("{pattern} => {}", body?.text));
                }
                Some(atom(tuple_match_spelling(
                    &scrutinee.text,
                    arms.len(),
                    &spelled_arms,
                )))
            }
            B::IntegerAddress(pointer, _) => {
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
    fn place_at(&mut self, pointer: &Address, depth: usize) -> String {
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
        memory: &SymbolicMemory,
        pointer: &Address,
        kind: crate::kernel::LoadKind,
        depth: usize,
    ) -> Option<Spelled> {
        if self.mode == Mode::ExactIdentity {
            return None;
        }
        let context = self
            .labels
            .source_memory_context(memory)
            .map(|(point, naming)| (point.len() <= 256, std::sync::Arc::new(naming.clone())));
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
        self.place_read_in(memory, |printer| {
            printer.load_place(&naming, pointer, kind, depth)
        })
    }

    /// The place a load reads, before its memory qualifies it.
    fn load_place(
        &mut self,
        naming: &Option<std::sync::Arc<NamingTables>>,
        pointer: &Address,
        kind: crate::kernel::LoadKind,
        depth: usize,
    ) -> Option<Spelled> {
        let cell = naming.as_deref().and_then(|naming| {
            if let Some(model) = crate::surface::diagnostics::diagnostic_model_load_cell(
                pointer,
                kind,
                ParameterBinding::new(&naming.0, &naming.1),
            ) {
                return Some((model, None));
            }
            if let Some((field, field_type)) =
                crate::surface::diagnostics::diagnostic_aggregate_parameter_load_cell(
                    pointer,
                    kind,
                    ParameterBinding::new(&naming.0, &naming.1),
                )
            {
                return Some((field, Some(field_type)));
            }
            // An address spelling alone does not establish the type of a
            // read. Keep only bases whose declared element has this exact
            // load kind.
            let (names, values): (Vec<_>, Vec<_>) = naming
                .0
                .iter()
                .zip(&naming.1)
                .filter(|(name, _)| name.name().len() <= 256)
                .filter(|(_, value)| match value {
                    crate::kernel::ProgramExpression::Value(
                        crate::kernel::ProgramValue::Pointer(base),
                    ) => base
                        .program_type()
                        .pointee_type()
                        .and_then(crate::kernel::LoadKind::of_type)
                        .is_some_and(|read| read.reads_word_of(kind)),
                    _ => true,
                })
                .map(|(name, value)| (name.clone(), value.clone()))
                .unzip();
            crate::surface::diagnostics::diagnostic_source_load_cell(
                pointer,
                kind,
                ParameterBinding::new(&names, &values),
            )
            .or_else(|| {
                crate::surface::diagnostics::diagnostic_loaded_field_load_cell(
                    pointer,
                    kind,
                    ParameterBinding::new(&naming.0, &naming.1),
                )
            })
            .map(|cell| (cell, None))
        });
        // The type a typed read's own spelling states, `*(p as (int64 *))`.
        let typed_read =
            (kind == crate::kernel::LoadKind::Bits64).then_some(crate::kernel::ProgramType::Int64);
        let (place, spelled_type) = match cell {
            Some((cell, field_type)) if !(self.source_mode() && cell.contains('+')) => {
                (atom(cell), field_type)
            }
            None if !self.source_mode() => return None,
            _ => {
                let address = self.pointer(pointer, depth)?;
                if let Some(place) = address.text.strip_prefix("the caller's ") {
                    // A by-value aggregate argument's field is a place of
                    // the caller's.
                    (atom(format!("the caller's {place}")), None)
                } else if address.text.starts_with("(char *)") && kind.byte_width() != 1 {
                    // A read at a byte offset reads the load's own type.
                    (
                        atom(format!(
                            "*({} *)({})",
                            load_type_spelling(kind),
                            address.text
                        )),
                        typed_read,
                    )
                } else if self.source_mode()
                    && Self::declared_element_differs(naming, pointer, kind)
                {
                    // A read whose type is not the named pointer's own
                    // element, a `uint8` read through a plain `char *`,
                    // states its type: a bare `*` reads the element type.
                    (
                        atom(format!(
                            "*({} as ({} *))",
                            address.text,
                            load_type_spelling(kind)
                        )),
                        typed_read,
                    )
                } else {
                    (atom(dereference(address)), None)
                }
            }
        };
        self.spelled_load_type = spelled_type;
        Some(place)
    }

    /// Whether a named pointer with this address's base declares an element
    /// that a `kind` read does not read.
    fn declared_element_differs(
        naming: &Option<std::sync::Arc<NamingTables>>,
        pointer: &Address,
        kind: crate::kernel::LoadKind,
    ) -> bool {
        naming.as_deref().is_some_and(|naming| {
            naming.1.iter().any(|value| match value {
                crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(
                    base,
                )) if base.address().base == pointer.base => base
                    .program_type()
                    .pointee_type()
                    .and_then(crate::kernel::LoadKind::of_type)
                    .is_some_and(|read| !read.reads_word_of(kind)),
                _ => false,
            })
        })
    }

    /// `place` read in `memory`.
    /// A fact checked in `memory`, spelled as a proof writes it: when the
    /// report has a current state and `memory` is another recorded point,
    /// `at(point, fact)`; otherwise bare. Unlike a read, a fact at entry is
    /// `at(function.entry, fact)`: `old` takes a value.
    fn qualify_fact(&mut self, memory: &SymbolicMemory, fact: Spelled) -> Option<Spelled> {
        let has_current = self
            .labels
            .source_memories
            .iter()
            .any(|(_, point, _)| point == "current");
        let point = self
            .labels
            .source_memory_context(memory)
            .map(|(point, _)| point.to_owned());
        Some(match point.as_deref() {
            Some(point) if has_current && point != "current" => {
                atom(format!("at({point}, {})", fact.text))
            }
            _ => fact,
        })
    }

    fn qualify(&mut self, memory: &SymbolicMemory, place: Spelled) -> Option<Spelled> {
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
    fn pointer(&mut self, pointer: &Address, depth: usize) -> Option<Spelled> {
        if pointer == &Address::null() {
            return Some(atom("0"));
        }
        // A slice binder's data pointer is `s.as_ptr()`, and an address past
        // it that pointer plus an element offset.
        if let crate::kernel::AddressBase::Symbolic(variable) = &pointer.base
            && let Some(element) = self.slice_bound.get(variable).copied()
            && let Some(name) = self.variable_name(*variable)
        {
            let data = atom(slice_component(
                "as_ptr",
                &name,
                element == crate::kernel::SliceElement::Str,
            ));
            let width = element
                .thin_pointer_type()
                .pointee_type()
                .map(|element| i64::from(element.byte_width()))
                .filter(|width| *width != 0)?;
            return Some(match pointer.offset.view() {
                OffsetView::Constant(0) => data,
                OffsetView::Constant(bytes) if bytes % width == 0 => {
                    spelled(format!("{} + {}", operand(data, ADD), bytes / width), ADD)
                }
                OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. } => {
                    let index = self.bitvector(index.structural_value(), None, depth + 1)?;
                    spelled(
                        format!("{} + {}", operand(data, ADD), operand(index, MULTIPLY)),
                        ADD,
                    )
                }
                _ => {
                    let offset = self.offset(&pointer.offset, depth + 1);
                    atom(format!("byte_offset({}, {offset})", data.text))
                }
            });
        }
        if let Some(name) = self.labels.pointer_sources.get(pointer) {
            // A reference parameter's carrier is spelled `&value`.
            let precedence = if name.starts_with('&') { UNARY } else { ATOM };
            return Some(spelled(name.clone(), precedence));
        }
        if let Some((name, _)) = super::c_library_pointer_name(pointer) {
            return Some(
                if matches!(pointer.offset.view(), OffsetView::Constant(0)) {
                    atom(name)
                } else {
                    let offset = self.offset(&pointer.offset, depth + 1);
                    atom(format!("byte_offset({name}, {offset})"))
                },
            );
        }
        // A pointer read from memory is the place it was read from.
        if let Some(read) = pointer.as_loaded_value() {
            let place =
                self.pointer_cell(read.defining_memory.memory(), &read.defining_address, depth);
            return Some(
                if matches!(read.displacement.view(), OffsetView::Constant(0)) {
                    place
                } else {
                    let offset = self.offset(&read.displacement, depth);
                    atom(format!("byte_offset({}, {offset})", place.text))
                },
            );
        }
        // The result of a pointer-valued pure call is that call, and an
        // address past it is that call plus an element offset, or a byte
        // offset from it.
        if let crate::kernel::AddressBase::PureFunctionApplication(application) = &pointer.base {
            let call = self.call(application.name(), application.arguments(), depth + 1)?;
            // A slice-valued call is the slice; its data pointer is
            // `f(x).as_ptr()`.
            let slice_element =
                crate::surface::diagnostics::slice_result_element(application.name());
            let call = match slice_element {
                Some(element) => atom(slice_component(
                    "as_ptr",
                    &call.text,
                    element == crate::kernel::SliceElement::Str,
                )),
                None => call,
            };
            return Some(match pointer.offset.view() {
                OffsetView::Constant(0) => call,
                OffsetView::Int32Scaled { index, .. } | OffsetView::Int64Scaled { index, .. } => {
                    let index = self.bitvector(index.structural_value(), None, depth + 1)?;
                    spelled(
                        format!("{} + {}", operand(call, ADD), operand(index, MULTIPLY)),
                        ADD,
                    )
                }
                OffsetView::Constant(bytes)
                    if let Some(width) = slice_element
                        .and_then(|element| element.thin_pointer_type().pointee_type())
                        .map(|element| i64::from(element.byte_width()))
                        .filter(|width| *width != 0)
                        .or_else(|| instance_element_width(application.name()))
                        && bytes % width == 0 =>
                {
                    spelled(format!("{} + {}", operand(call, ADD), bytes / width), ADD)
                }
                _ => {
                    let offset = self.offset(&pointer.offset, depth + 1);
                    atom(format!("byte_offset({}, {offset})", call.text))
                }
            });
        }
        if !self.source_mode() {
            return None;
        }
        if let Some(OldMachineTerm::MemoryLoad(memory, address, _)) =
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
        if self.before_return
            && self
                .labels
                .state_pointer_name(pointer)
                .is_some_and(names_result)
        {
            return Some(atom(self.labels.placeholder_pointer(pointer)));
        }
        // An address past a pointer parameter by a term the structural
        // spellings cannot name, such as a quantifier binder, is an element
        // of that parameter, `&dst[k]`, or a byte offset from it.
        if let Some(tables) = tables.as_deref()
            && let Some(spelled) = self.parameter_relative_pointer(pointer, depth, tables)
        {
            return Some(spelled);
        }
        // An address inside an allocation a local held is spelled from that
        // local: `(char *)at(region(2).exit, p) + k * 4`.
        if self.labels.state_pointer_name(pointer).is_none()
            && !matches!(pointer.offset.view(), OffsetView::Constant(0))
            && let Some(base) = self.labels.block_base_name(pointer).map(str::to_owned)
            && base.len() <= 256
        {
            let offset = self.offset(&pointer.offset, depth);
            return Some(spelled(format!("(char *){base} + {offset}"), 0));
        }
        Some(atom(self.labels.unnamed_pointer(pointer)))
    }

    /// The pointer stored at `address` in `memory`, as the place it is read
    /// from.
    fn pointer_cell(
        &mut self,
        memory: &SymbolicMemory,
        address: &Address,
        depth: usize,
    ) -> Spelled {
        let tables = self.labels.naming.clone();
        let cell = tables.as_deref().and_then(|(parameters, arguments)| {
            let binding = ParameterBinding::new(parameters, arguments);
            crate::surface::diagnostics::diagnostic_source_pointer_cell(address, binding, None)
                .or_else(|| crate::surface::diagnostics::diagnostic_source_cell(address, binding))
                .or_else(|| {
                    address.as_loaded_value()?;
                    crate::surface::diagnostics::diagnostic_load_place(address, binding)
                })
        });
        self.place_read_in(memory, |printer| {
            Some(match cell {
                Some(cell) => atom(cell),
                None => match printer.pointer(address, depth) {
                    Some(address) => atom(dereference(address)),
                    None => atom("…"),
                },
            })
        })
        .unwrap_or_else(|| atom("…"))
    }

    /// A byte range as Click writes a viewable range: in elements of the
    /// base's declared type when its width divides the byte count, and in
    /// bytes otherwise.
    fn byte_range(
        &mut self,
        base: &Address,
        bytes: &OldMachineTerm,
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
                bits32_constant!(value) if i64::from(constant_u32(*value)) % width == 0 => {
                    Some(atom((i64::from(constant_u32(*value)) / width).to_string()))
                }
                uint64_constant!(value) if (constant_u64(*value) as i64) % width == 0 => {
                    Some(atom(format!("{}u64", constant_u64(*value) as i64 / width)))
                }
                binary_term!(Int32, Multiply, left, right)
                | OldMachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Multiply,
                    left,
                    right,
                } if right.as_const().map(i64::from) == Some(width) => {
                    self.bitvector(left, hint, depth)
                }
                binary_term!(Int32, Multiply, left, right)
                | OldMachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Multiply,
                    left,
                    right,
                } if left.as_const().map(i64::from) == Some(width) => {
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
                format!("({} as (uint8 *))[0..{bytes}]", operand(address, CAST))
            }
        }
    }

    /// The referent a C++ reference parameter names when `pointer` is the
    /// address it carries: `value` for `int32& value`, and the field at its
    /// start for a struct referent. The sidecar writes the referent, never
    /// the carrier.
    fn reference_referent(&self, pointer: &Address) -> Option<String> {
        let tables = self.labels.naming.as_deref()?;
        tables
            .0
            .iter()
            .zip(&tables.1)
            .find_map(|(parameter, value)| {
                let crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(
                    base,
                )) = value
                else {
                    return None;
                };
                if !parameter.is_reference() || base.address() != pointer {
                    return None;
                }
                let referent = parameter.name();
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
                crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(
                    _,
                )) if parameter.name() == name => {
                    Some(crate::surface::diagnostics::diagnostic_parameter_element_width(parameter))
                }
                _ => None,
            })
            .filter(|width| *width > 0)
    }

    /// `pointer` as an element of, or a byte offset from, a pointer
    /// parameter whose value is `pointer` less one added offset term.
    fn parameter_relative_pointer(
        &mut self,
        pointer: &Address,
        depth: usize,
        tables: &NamingTables,
    ) -> Option<Spelled> {
        let OffsetView::Add(base_offset, extra) = pointer.offset.view() else {
            return None;
        };
        let parameter =
            tables
                .0
                .iter()
                .zip(&tables.1)
                .find_map(|(parameter, value)| match value {
                    crate::kernel::ProgramExpression::Value(
                        crate::kernel::ProgramValue::Pointer(base),
                    ) if base.address().base == pointer.base
                        && base.address().offset == *base_offset
                        && parameter.name().len() <= 256 =>
                    {
                        Some(parameter)
                    }
                    _ => None,
                })?;
        let name = parameter.name();
        let width = crate::surface::diagnostics::diagnostic_parameter_element_width(parameter);
        let index = match extra.view() {
            OffsetView::Int32Scaled { index, byte_width }
            | OffsetView::Int64Scaled {
                index, byte_width, ..
            } if byte_width == width && width > 0 => {
                self.bitvector(index.structural_value(), None, depth + 1)
            }
            _ => None,
        };
        Some(match index {
            Some(index) => spelled(format!("&{name}[{}]", index.text), UNARY),
            // A slice's byte offsets are from its data pointer.
            None if matches!(
                parameter.interface_type(),
                crate::languages::interface::InterfaceType::Slice(_)
            ) =>
            {
                spelled(
                    format!(
                        "(char *){name}.as_ptr() + {}",
                        self.offset(extra, depth + 1)
                    ),
                    0,
                )
            }
            None => spelled(
                format!("(char *){name} + {}", self.offset(extra, depth + 1)),
                0,
            ),
        })
    }

    /// The element width of the pointer a naming table binds to `base`.
    fn element_width(&self, base: &Address) -> Option<i64> {
        let tables = self.labels.naming.as_deref()?;
        tables
            .0
            .iter()
            .zip(&tables.1)
            .find_map(|(parameter, value)| match value {
                crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(
                    pointer,
                )) if pointer.address() == base => {
                    Some(crate::surface::diagnostics::diagnostic_parameter_element_width(parameter))
                }
                _ => None,
            })
            .filter(|width| *width > 0)
    }

    fn resource_fact(&mut self, fact: &ResourceFact) -> String {
        if !self.source_mode() {
            return super::render_resource_fact_labeled(fact, self.labels);
        }
        if matches!(fact.resource(), Resource::ConditionalMutexGuard(_)) {
            return self.resource(fact.resource());
        }
        let text = self.resource(fact.resource());
        match fact {
            ResourceFact::View(_) => format!("views {text}"),
            ResourceFact::Own(_, quantity) if quantity.as_const() == Some(1) => {
                format!("owns {text}")
            }
            ResourceFact::Own(_, quantity) => {
                let quantity = self
                    .bitvector(quantity.old_form(), None, 0)
                    .map_or_else(|| "…".into(), |v| v.text);
                format!("owns {text} (quantity {quantity})")
            }
        }
    }

    fn resource_arguments(&mut self, name: &str, arguments: &[AlgebraicValue]) -> String {
        let mut spelled = Vec::new();
        for (index, argument) in arguments.iter().enumerate() {
            if self.remaining == 0 {
                spelled.push(format!(
                    "… {} more arguments omitted",
                    arguments.len() - index
                ));
                break;
            }
            spelled.push(
                match argument {
                    AlgebraicValue::Program(value) => self.cvalue(value, 0),
                    AlgebraicValue::Integer(value) => self.integer(value, 0),
                    AlgebraicValue::Algebraic(value) => self.algebraic(value, 0),
                }
                .map_or_else(|| "…".into(), |v| v.text),
            );
        }
        format!("{name}({})", spelled.join(", "))
    }

    /// The hidden record of a resource that declares no fields: the fields
    /// it keeps for its named children, `record { first.v: <unnamed A> }`,
    /// spelled as a fold's field map is. `None` for an instance with a
    /// declared field, whose fields the reader names.
    fn hidden_record(
        &mut self,
        schema: &[(String, crate::kernel::ResourceFieldType)],
        fields: &[AlgebraicValue],
    ) -> Option<String> {
        let names = schema
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>();
        hidden_record_fields(&names)?;
        let mut entries = Vec::new();
        for (index, (name, value)) in names.iter().zip(fields).enumerate() {
            if self.remaining == 0 {
                entries.push(format!("… {} more fields omitted", names.len() - index));
                break;
            }
            let value = match value {
                AlgebraicValue::Program(value) => self.cvalue(value, 0),
                AlgebraicValue::Integer(value) => self.integer(value, 0),
                AlgebraicValue::Algebraic(value) => self.algebraic(value, 0),
            }
            .map_or_else(|| "…".into(), |value| value.text);
            entries.push(format!("{name}: {value}"));
        }
        Some(format!("record {{ {} }}", entries.join(", ")))
    }

    fn resource_subject(&mut self, resource: &Resource) -> String {
        match resource {
            Resource::Memory(_) => format!("memory({})", self.resource(resource)),
            Resource::Star(pair) => format!(
                "({} * {})",
                self.resource_subject(&pair.0),
                self.resource_subject(&pair.1),
            ),
            _ => self.resource(resource),
        }
    }

    fn resource(&mut self, resource: &Resource) -> String {
        if !self.source_mode() {
            let text = super::render_resource_fact_labeled(
                &ResourceFact::View(resource.clone()),
                self.labels,
            );
            return text.strip_prefix("views ").unwrap_or(&text).to_owned();
        }
        let tables = self.labels.naming.clone();
        let (parameters, arguments) = tables
            .as_deref()
            .map_or((&[][..], &[][..]), |(p, a)| (p.as_slice(), a.as_slice()));
        let binding = ParameterBinding::new(parameters, arguments);
        match resource {
            Resource::Emp => "separation::emp".into(),
            Resource::Star(pair) => {
                format!("({} * {})", self.resource(&pair.0), self.resource(&pair.1))
            }
            Resource::Footprint(fp) => fp.source.clone(),
            Resource::Parameter(v) => self
                .variable_name(*v)
                .unwrap_or_else(|| self.unnamed_variable(*v)),
            Resource::Memory(range) => {
                let text = crate::surface::diagnostics::describe_memory_range(range, binding);
                if !text.starts_with('…') {
                    return text;
                }
                // A base only a recorded state names, a call's result.
                let (parameters, arguments) = self.labels.naming_with_state_values();
                crate::surface::diagnostics::describe_memory_range(
                    range,
                    ParameterBinding::new(&parameters, &arguments),
                )
            }
            Resource::Instance(instance) => {
                let application = self
                    .resource_arguments(instance.name(), &(instance.arguments()).native_values());
                match self.hidden_record(
                    instance.schema().fields(),
                    &instance.fields().native_values(),
                ) {
                    Some(record) => format!("{application} {record}"),
                    None => application,
                }
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => self
                .resource_arguments(
                    &crate::languages::display_source_names(name),
                    &(arguments).native_values(),
                ),
            Resource::ConditionalMutexGuard(carrier) => {
                let condition = self
                    .condition(carrier.condition(), true, 0)
                    .expect("scalar loop condition has source syntax")
                    .text;
                let mutex =
                    crate::surface::diagnostics::describe_mutex_pointer(carrier.mutex(), binding);
                format!("if {condition} {{ owns mutex_guard({mutex}); }}")
            }
            Resource::MutexGuard(identity) => format!(
                "mutex_guard({})",
                crate::surface::diagnostics::describe_mutex_pointer(identity.mutex(), binding)
            ),
            Resource::MutexLive(identity) => format!(
                "mutex_live({})",
                crate::surface::diagnostics::describe_mutex_pointer(identity.mutex(), binding)
            ),
            Resource::MutexUse(identity) => {
                let mutex =
                    crate::surface::diagnostics::describe_mutex_pointer(identity.mutex(), binding);
                match identity.protected_type() {
                    Some(ty) => {
                        let protected =
                            self.resource_arguments(ty.family(), &(ty.arguments()).native_values());
                        format!("mutex_use({mutex}, {protected})")
                    }
                    None => format!("mutex_use({mutex})"),
                }
            }
            Resource::Publication(right) => {
                let flag =
                    crate::surface::diagnostics::describe_mutex_pointer(right.flag(), binding);
                let payload = self.resource_arguments(
                    right.payload().family(),
                    &(right.payload().arguments()).native_values(),
                );
                let mut text = format!("{}({flag}, {payload})", right.side().keyword());
                if right.observed().is_some() {
                    text.push_str(
                        ", read by an acquire load whose value no C branch has tested yet",
                    );
                }
                text
            }
            Resource::PopulationAuthority(description) => {
                let mut text = self.resource_arguments(
                    description.family(),
                    &(description.arguments()).native_values(),
                );
                if let Some(arity) = description.population_arity() {
                    text.pop();
                    for _ in 1..arity {
                        text.push_str(", _");
                    }
                    text.push(')');
                }
                format!("authority({text})")
            }
            Resource::Iterated(iterated) => {
                crate::surface::diagnostics::describe_iterated_memory(iterated, binding)
            }
        }
    }

    fn cvalue(&mut self, value: &crate::kernel::ProgramValue, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        let depth = depth + 1;
        use crate::kernel::ProgramValue;
        if !self.source_mode() {
            return match value {
                ProgramValue::Bool(value) if value.bool_constant_value() == Some(false) => {
                    Some(atom("false"))
                }
                ProgramValue::Bool(value) if value.bool_constant_value() == Some(true) => {
                    Some(atom("true"))
                }
                ProgramValue::Bool(value)
                | ProgramValue::Int64(value)
                | ProgramValue::UInt64(value) => self.bitvector(value, None, depth),
                ProgramValue::Int32(value) => self
                    .exact_operand(value, Some(true), depth)
                    .map(|text| spelled(text, SHIFT)),
                ProgramValue::UInt32(value) => self
                    .exact_operand(value, Some(false), depth)
                    .map(|text| spelled(text, SHIFT)),
                ProgramValue::Pointer(pointer) => {
                    let naming = self.labels.naming.clone()?;
                    self.exact_pointer_value(pointer, &naming).map(atom)
                }
                _ => None,
            };
        }
        let typed = |printer: &mut Self, value: &OldMachineTerm, hint: Hint, suffix: &str| {
            let spelled_value = printer.bitvector(value, Some(hint), depth)?;
            Some(match value {
                bits32_constant!(_) | native_constant!(_, _) if !suffix.is_empty() => {
                    atom(typed_literal(spelled_value.text, suffix))
                }
                _ => spelled_value,
            })
        };
        match value.numeric_value() {
            ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
            ProgramValue::Parameter(term) => self.algebraic(term, depth),
            ProgramValue::Void => Some(atom("void")),
            ProgramValue::Bool(value) if value.bool_constant_value() == Some(false) => {
                Some(atom("false"))
            }
            ProgramValue::Bool(value) if value.bool_constant_value() == Some(true) => {
                Some(atom("true"))
            }
            ProgramValue::Bool(value) => {
                self.bitvector(value, Some(Hint::Narrow { signed: false }), depth)
            }
            ProgramValue::Int8(value) => typed(self, value, Hint::Narrow { signed: true }, "i8"),
            ProgramValue::Int16(value) => typed(self, value, Hint::Narrow { signed: true }, "i16"),
            ProgramValue::UInt8(value) => typed(self, value, Hint::Narrow { signed: false }, "u8"),
            ProgramValue::UInt16(value) => {
                typed(self, value, Hint::Narrow { signed: false }, "u16")
            }
            ProgramValue::Int32(value) => typed(self, value, Hint::Signed32, ""),
            ProgramValue::UInt32(value) => typed(self, value, Hint::Unsigned32, ""),
            ProgramValue::Int64(value) => typed(self, value, Hint::Int64, ""),
            ProgramValue::UInt64(value) => typed(self, value, Hint::UInt64, ""),
            ProgramValue::Int128(value) | ProgramValue::UInt128(value) => {
                self.bitvector(value, None, depth)
            }
            value @ (ProgramValue::Float32(_) | ProgramValue::Float64(_))
                if crate::surface::diagnostics::exact_float_literal_spelling(value).is_some() =>
            {
                Some(atom(
                    crate::surface::diagnostics::exact_float_literal_spelling(value).unwrap(),
                ))
            }
            ProgramValue::Float32(value) | ProgramValue::Float64(value) => {
                self.bitvector(value, None, depth)
            }
            ProgramValue::Pointer(pointer) if pointer.is_wide() => self.slice(pointer, depth),
            ProgramValue::Pointer(pointer) => self.pointer(pointer.address(), depth),
        }
    }

    /// A slice (`design/rust-slice-values.md`): the one value that names
    /// it, where one does (a binder or parameter, a slice-valued pure call,
    /// a slice cell's place), a subslice the kernel recorded where it was
    /// built as written, `bytes[a..b]`, and any other slice as its
    /// construction, `slice::from_raw_parts(p, n)`.
    fn slice(&mut self, slice: &crate::kernel::Pointer, depth: usize) -> Option<Spelled> {
        let string = slice.program_type()
            == crate::kernel::ProgramType::SlicePointer(crate::kernel::SliceElement::Str);
        let spelled = self.slice_at_own_type(slice, depth)?;
        // A slice whose type is not its name's is that name retyped
        // (`design/rust-slice-values.md`, "String slices").
        Some(match (spelled.1, string) {
            (true, false) => atom(str_operation("as_bytes", &spelled.0.text)),
            (false, true) => atom(str_operation("from_utf8_unchecked", &spelled.0.text)),
            _ => spelled.0,
        })
    }

    /// A slice as the value that names it or its construction, with whether
    /// that spelling's own type is the string slice `Str`.
    fn slice_at_own_type(
        &mut self,
        slice: &crate::kernel::Pointer,
        depth: usize,
    ) -> Option<(Spelled, bool)> {
        let string = slice.program_type()
            == crate::kernel::ProgramType::SlicePointer(crate::kernel::SliceElement::Str);
        let count = slice.len()?;
        // A parameter's own slice is its name.
        if let Some(naming) = self.labels.naming.clone()
            && let Some(name) = self.exact_pointer_value(slice, &naming)
        {
            return Some((atom(name), string));
        }
        let thin = slice.as_ptr();
        let address = thin.address();
        if matches!(address.offset.view(), OffsetView::Constant(0)) {
            match (&address.base, count) {
                (
                    crate::kernel::AddressBase::Symbolic(variable),
                    OldMachineTerm::Variable(counted),
                ) if counted.counted_slice() == Some(*variable) => {
                    let named = self.slice_bound.get(variable).map_or(string, |element| {
                        *element == crate::kernel::SliceElement::Str
                    });
                    // A slice a recorded state held is that local, not its
                    // data pointer's spelling.
                    if let Some((name, _)) = self.labels.recorded_slice_name(count) {
                        return Some((atom(name.to_owned()), named));
                    }
                    return Some((self.pointer(address, depth)?, named));
                }
                (
                    crate::kernel::AddressBase::PureFunctionApplication(application),
                    OldMachineTerm::PureApplicationCount(counted),
                ) if application == counted => {
                    let named =
                        crate::surface::diagnostics::slice_result_element(application.name())
                            .map_or(string, |element| {
                                element == crate::kernel::SliceElement::Str
                            });
                    return Some((
                        self.call(application.name(), application.arguments(), depth + 1)?,
                        named,
                    ));
                }
                (
                    crate::kernel::AddressBase::SliceData(load),
                    OldMachineTerm::MemoryLoad(_, read, crate::kernel::LoadKind::SliceCount),
                ) if read.load() == load => {
                    return Some((atom(self.place_at(load.cell(), depth)), string));
                }
                _ => {}
            }
        }
        let data = self.slice_data(address, depth)?.text;
        let count = self.bitvector(count, Some(Hint::UInt64), depth)?.text;
        // A subslice the kernel recorded where it was built, whose bounds
        // were owed there, is spelled as written.
        if crate::surface::diagnostics::rust_spelling()
            && crate::kernel::is_required_construction(slice)
            && let Some(subslice) = crate::surface::diagnostics::subslice_spelling(&data, &count)
        {
            return Some((atom(subslice), false));
        }
        let name = if crate::surface::diagnostics::rust_spelling() {
            crate::surface::RUST_SLICE_FROM_RAW_PARTS
        } else {
            "slice::from_raw_parts"
        };
        Some((atom(format!("{name}({data}, {count})")), false))
    }

    /// A slice's data pointer: `s.as_ptr()` of a slice cell's place, else
    /// the thin pointer's own spelling.
    fn slice_data(&mut self, address: &Address, depth: usize) -> Option<Spelled> {
        if let crate::kernel::AddressBase::SliceData(load) = &address.base
            && matches!(address.offset.view(), OffsetView::Constant(0))
        {
            let place = self.place_at(load.cell(), depth);
            return Some(atom(slice_component("as_ptr", &place, false)));
        }
        self.pointer(address, depth)
    }

    /// A slice's count, `s.len()` of the slice that names it: a slice a
    /// variable names, a slice-valued pure call, or a slice cell's place.
    fn slice_count(&mut self, count: &OldMachineTerm, depth: usize) -> Option<Spelled> {
        let (slice, string) = match count {
            // The slice a name holds whose count this is: `bytes.len()` for
            // a local `bytes` holding a call's slice result, whose data
            // pointer is the variable the count counts and is named
            // `bytes.as_ptr()`.
            OldMachineTerm::Variable(_)
                if let Some(naming) = self.labels.naming.clone()
                    && let Some((name, element)) = counted_slice_name(count, &naming) =>
            {
                (name, element == crate::kernel::SliceElement::Str)
            }
            // A slice a recorded state's local or call result held.
            OldMachineTerm::Variable(_)
                if let Some((name, string)) = self.labels.recorded_slice_name(count) =>
            {
                (name.to_owned(), string)
            }
            OldMachineTerm::Variable(counted) => {
                let variable = counted.counted_slice()?;
                (
                    self.pointer(&Address::symbolic(variable), depth)?.text,
                    self.slice_bound.get(&variable) == Some(&crate::kernel::SliceElement::Str),
                )
            }
            OldMachineTerm::PureApplicationCount(application) => (
                self.call(application.name(), application.arguments(), depth + 1)?
                    .text,
                crate::surface::diagnostics::slice_result_element(application.name())
                    == Some(crate::kernel::SliceElement::Str),
            ),
            OldMachineTerm::MemoryLoad(_, read, crate::kernel::LoadKind::SliceCount) => {
                (self.place_at(read.load().cell(), depth), false)
            }
            _ => return None,
        };
        Some(atom(slice_component("len", &slice, string)))
    }

    fn exact_pointer_value(
        &self,
        pointer: &crate::kernel::Pointer,
        naming: &NamingTables,
    ) -> Option<String> {
        if self.mode == Mode::ExactIdentity
            && crate::surface::proof_trace::pointer_definition(pointer.address()).is_some()
        {
            return None;
        }
        naming
            .0
            .iter()
            .zip(&naming.1)
            .find_map(|(name, value)| match value {
                crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(
                    base,
                )) if base == pointer
                    && base.program_type() == pointer.program_type()
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
            // Explicit output boundary of the native diagnostic renderer.
            PureFunctionArgument::SharedMachine(value) => self.cvalue(
                &value.ty().value_from_term(value.structural_value().clone()),
                depth + 1,
            ),
            PureFunctionArgument::Integer(value) => self.integer(value, depth + 1),
            PureFunctionArgument::Algebraic(value) => self.algebraic(value, depth + 1),
            PureFunctionArgument::ArrayRef {
                point: memory,
                pointer: crate::kernel::ProgramValue::Pointer(pointer),
                element_type,
            } => {
                if !self.source_mode() {
                    if pointer.program_type().pointee_type() != Some(*element_type)
                        || self.mode == Mode::ExactIdentity
                    {
                        return None;
                    }
                    let (point, naming) = self.labels.source_memory_context(memory.memory())?;
                    let (point, naming) = (point.to_owned(), naming.clone());
                    let name = self.exact_pointer_value(pointer, &naming)?;
                    return Some(atom(if point == "current" {
                        name
                    } else {
                        format!("at({point}, {name})")
                    }));
                }
                self.place_read_in(memory.memory(), |printer| {
                    printer.pointer(pointer.address(), depth + 1)
                })
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
        if let Some(text) =
            crate::surface::diagnostics::slice_call_spelling(name, &spelled_arguments)
        {
            return Some(atom(text));
        }
        let text = format!("{name}({})", spelled_arguments.join(", "));
        (text.len() <= 2048 || self.source_mode()).then(|| atom(text))
    }

    fn algebraic(&mut self, value: &AlgebraicTerm, depth: usize) -> Option<Spelled> {
        if let Err(elided) = self.enter(depth) {
            return elided;
        }
        match &value.node {
            AlgebraicTermNode::Variable(variable) => self
                .variable_name(*variable)
                .or_else(|| {
                    // This alias is for reports. Exact modes require their
                    // own checked source spellings.
                    self.source_mode()
                        .then(|| self.labels.current_algebraic_field_name(*variable, value))
                        .flatten()
                })
                .or_else(|| crate::kernel::model_fields::entry_model_field_surface(*variable))
                .map(atom)
                .or_else(|| self.placeholder(|printer| printer.unnamed_variable(*variable))),
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                self.call(name, arguments, depth + 1)
            }
            AlgebraicTermNode::MemoryLoad {
                point: memory,
                pointer,
            } => self.bitvector(
                &AlgebraicTermNode::memory_load_carrier(memory, pointer, &value.algebraic_type),
                None,
                depth + 1,
            ),
            AlgebraicTermNode::Constructor { variant, fields } => {
                if value.algebraic_type.name.len() + variant.len() > 256 {
                    return None;
                }
                let mut spelled_fields = Vec::new();
                for field in fields {
                    spelled_fields.push(
                        match field {
                            AlgebraicValue::Program(value) => self.cvalue(value, depth + 1),
                            AlgebraicValue::Integer(value) => self.integer(value, depth + 1),
                            AlgebraicValue::Algebraic(value) => self.algebraic(value, depth + 1),
                        }?
                        .text,
                    );
                }
                // A struct's value, `*p` or a literal of its fields.
                if value.algebraic_type.name == *variant
                    && value.algebraic_type.arguments.is_empty()
                    && let Some(spelled) = crate::surface::struct_values::spell(
                        &value.algebraic_type.name,
                        &spelled_fields,
                    )
                {
                    return Some(atom(spelled));
                }
                if crate::surface::tuples::arity(variant).is_some() {
                    return Some(atom(crate::surface::tuples::spell(&spelled_fields)));
                }
                let name = format!("{}::{variant}", value.algebraic_type.name);
                Some(atom(if spelled_fields.is_empty() {
                    name
                } else {
                    format!("{name}({})", spelled_fields.join(", "))
                }))
            }
            AlgebraicTermNode::If {
                condition,
                then_term,
                else_term,
            } => {
                let condition = self.condition(condition, true, depth + 1)?;
                let then_term = self.algebraic(then_term, depth + 1)?;
                let else_term = self.algebraic(else_term, depth + 1)?;
                Some(spelled(
                    format!(
                        "if {} {{ {} }} else {{ {} }}",
                        condition.text, then_term.text, else_term.text
                    ),
                    0,
                ))
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                if !self.source_mode() {
                    return None;
                }
                let scrutinee = self.algebraic(scrutinee, depth + 1)?;
                let mut spelled_arms = Vec::new();
                for arm in arms {
                    let (pattern, bound) =
                        self.arm_pattern(&arm.variant, &arm.bindings, &arm.binding_names);
                    let body = self.algebraic(&arm.body, depth + 1);
                    self.bound.truncate(self.bound.len() - bound);
                    spelled_arms.push(format!("{pattern} => {}", body?.text));
                }
                Some(atom(tuple_match_spelling(
                    &scrutinee.text,
                    arms.len(),
                    &spelled_arms,
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
            IntegerTerm::Variable(variable)
                if self.variable_name(*variable).is_none()
                    && crate::kernel::model_fields::registered_model_field_origin(*variable)
                        .is_some() =>
            {
                match crate::kernel::model_fields::entry_model_field_surface(*variable) {
                    Some(field) => Some(atom(field)),
                    None => self.placeholder(|printer| printer.unnamed_variable(*variable)),
                }
            }
            IntegerTerm::Variable(variable) => match self
                .bound
                .iter()
                .rev()
                .find(|(bound, _)| bound == variable)
                .map(|(_, name)| name.clone())
                .or_else(|| self.labels.integer_name_for(*variable).map(str::to_owned))
                .or_else(|| self.variable_name(*variable))
                .or_else(|| crate::kernel::model_fields::model_field_surface(*variable))
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
                let value = self.operand_as(value.value(), hint, depth)?;
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
            IntegerTerm::If {
                condition,
                then_term,
                else_term,
            } => {
                let condition = self.condition(condition, true, depth)?;
                let then_term = self.integer(then_term, depth)?;
                let else_term = self.integer(else_term, depth)?;
                // Parenthesized wherever it is an operand, as a machine
                // conditional is.
                Some(spelled(
                    format!(
                        "if {} {{ {} }} else {{ {} }}",
                        condition.text, then_term.text, else_term.text
                    ),
                    0,
                ))
            }
            IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
                let scrutinee = self.algebraic(scrutinee, depth)?;
                let mut spelled_arms = Vec::new();
                for arm in arms {
                    let (pattern, bound) =
                        self.arm_pattern(&arm.variant, &arm.bindings, &arm.binding_names);
                    let body = self.integer(&arm.body, depth);
                    self.bound.truncate(self.bound.len() - bound);
                    spelled_arms.push(format!("{pattern} => {}", body?.text));
                }
                Some(atom(tuple_match_spelling(
                    &scrutinee.text,
                    arms.len(),
                    &spelled_arms,
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

fn load_type_spelling(kind: crate::kernel::LoadKind) -> &'static str {
    use crate::kernel::LoadKind as K;
    match kind {
        K::Int8 => "int8",
        K::UInt8 => "uint8",
        K::Int16 => "int16",
        K::UInt16 => "uint16",
        K::Int32 => "int32",
        K::UInt32 => "uint32",
        // An algebraic read keeps the spelling of the eight-byte stand-in it
        // had before it was decoded at its own type (`design/loads.md`, step
        // 3b PR 2); a `load<T>` spelling is open question 1's to settle.
        K::Bits64 | K::Algebraic(_) => "int64",
        K::Int128 => "int128",
        K::UInt128 => "uint128",
        K::Float32 => "float",
        K::Float64 => "double",
        // A slice's count is `s.len()` of the slice read
        // (`Printer::slice_count`); it is never a typed read of a word of the
        // cell, so no read spells this type.
        K::SliceCount => "usize",
    }
}

/// `s.len()` or `s.as_ptr()` of the slice spelled `slice`, in the Rust
/// spelling where the function is written in Rust syntax and as the
/// library call elsewhere.
/// A slice's component, `len` or `as_ptr`, as Rust's method or the
/// library function of its type: `str::len(s)` for a string slice.
fn slice_component(component: &str, slice: &str, string: bool) -> String {
    if string {
        str_operation(component, slice)
    } else if crate::surface::diagnostics::rust_spelling() {
        format!("{slice}.{component}()")
    } else {
        format!("slice::{component}({slice})")
    }
}

/// A string slice operation of `click::rust::str` applied to `operand`, as
/// Rust's method, `s.as_bytes()`, or the library call.
fn str_operation(operation: &str, operand: &str) -> String {
    match (crate::surface::diagnostics::rust_spelling(), operation) {
        (true, "from_utf8_unchecked") => {
            format!("click::rust::str::from_utf8_unchecked({operand})")
        }
        (true, _) => format!("{operand}.{operation}()"),
        (false, _) => format!("str::{operation}({operand})"),
    }
}

fn algebraic_type_spelling(name: &str, arguments: &[AlgebraicValueType]) -> String {
    if arguments.is_empty() {
        return name.to_owned();
    }
    let arguments = arguments
        .iter()
        .map(|argument| match argument {
            AlgebraicValueType::Parameter(name) => name.clone(),
            AlgebraicValueType::ObjectPointer(_, class) => format!("{}*", class.spelling()),
            AlgebraicValueType::Program(ty) => crate::kernel::program_type_spelling(*ty).to_owned(),
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
/// Whether a registered source name is the function outcome's `result`.
fn names_result(name: &str) -> bool {
    matches!(name, "result" | "&result")
}

/// The element width of the pointer a generic pure function's instance
/// returns, read from its instance name: one byte for
/// `click::rust::slice::as_ptr::<uint8>`.
fn instance_element_width(name: &str) -> Option<i64> {
    let (_, instance) = name.split_once("::<")?;
    Some(match instance.strip_suffix('>')? {
        "int8" | "uint8" => 1,
        "int16" | "uint16" => 2,
        "int32" | "uint32" => 4,
        "int64" | "uint64" => 8,
        _ => return None,
    })
}

fn dereference(address: Spelled) -> String {
    if address.precedence == UNARY
        && let Some(place) = address.text.strip_prefix('&')
        && !place.contains(' ')
    {
        return place.to_owned();
    }
    // An element of a slice value, read through its data pointer, is
    // written as Rust writes it: `x[i]`.
    if let Some(slice) = address.text.strip_suffix(".as_ptr()")
        && address.precedence == ATOM
    {
        return format!("{slice}[0]");
    }
    if address.precedence == ADD
        && let Some((slice, index)) = address.text.split_once(".as_ptr() + ")
        && !index.contains(' ')
    {
        return format!("{slice}[{index}]");
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
    use crate::kernel::{AddressBase, LoadKind, Pointer, ProgramType, ProgramValue, SharedMemory};

    fn equality(value: OldMachineTerm) -> Proposition {
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(value),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        )
    }

    #[test]
    fn float_diagnostics_keep_names_widths_and_exact_bits() {
        let parameters = [
            crate::languages::interface::ImportedParameter::new(
                crate::languages::interface::InterfaceType::Float64,
                "d".into(),
                None,
            ),
            crate::languages::interface::ImportedParameter::new(
                crate::languages::interface::InterfaceType::Float32,
                "f".into(),
                None,
            ),
        ];
        let arguments = [
            crate::kernel::ProgramExpression::Value(ProgramValue::Float64(
                OldMachineTerm::Variable(Variable(7)),
            )),
            crate::kernel::ProgramExpression::Value(ProgramValue::Float32(
                OldMachineTerm::Variable(Variable(8)),
            )),
        ];
        let mut labels = MemoryStateLabels::naming(ParameterBinding::new(&parameters, &arguments));
        for (value, expected) in [
            (
                -2147483648.0_f64,
                "d >= float64_from_bits(0xc1e0000000000000u64)",
            ),
            (
                2147483648.0,
                "d >= float64_from_bits(0x41e0000000000000u64)",
            ),
            (-0.0, "d >= float64_from_bits(0x8000000000000000u64)"),
            (0.0, "d >= float64_from_bits(0x0000000000000000u64)"),
            (1.5, "d >= float64_from_bits(0x3ff8000000000000u64)"),
        ] {
            let fact = Proposition::condition_is(
                OldConditionTerm::Float64(crate::kernel::FloatCondition::Comparison {
                    operator: crate::kernel::ComparisonOperator::GreaterEqual,
                    left: Box::new(OldMachineTerm::Variable(Variable(7))),
                    right: Box::new(OldMachineTerm::uint64_constant(value.to_bits())),
                }),
                true,
            );
            assert_eq!(source(&fact, &mut labels), expected);
        }
        let fact = Proposition::condition_is(
            OldConditionTerm::Float32(crate::kernel::FloatCondition::Comparison {
                operator: crate::kernel::ComparisonOperator::LessThan,
                left: Box::new(OldMachineTerm::Float32Binary {
                    operator: crate::kernel::FloatBinaryOperator::Add,
                    left: Box::new(OldMachineTerm::Variable(Variable(8))),
                    right: Box::new(OldMachineTerm::constant(1.5_f32.to_bits())),
                }),
                right: Box::new(OldMachineTerm::constant(2.0_f32.to_bits())),
            }),
            true,
        );
        assert_eq!(
            source(&fact, &mut labels),
            "f + float32_from_bits(0x3fc00000) < float32_from_bits(0x40000000)"
        );
        let widened = Proposition::condition_is(
            OldConditionTerm::float64_compare(
                OldMachineTerm::PureFunctionApplication {
                    name: "c_float32_to_float64".into(),
                    arguments: vec![OldMachineTerm::Float32Binary {
                        operator: crate::kernel::FloatBinaryOperator::Multiply,
                        left: Box::new(OldMachineTerm::Variable(Variable(8))),
                        right: Box::new(OldMachineTerm::constant(2.0_f32.to_bits())),
                    }],
                },
                OldMachineTerm::uint64_constant(16.0_f64.to_bits()),
                crate::kernel::ComparisonOperator::LessThan,
            ),
            true,
        );
        assert_eq!(
            source(&widened, &mut labels),
            "(f * float32_from_bits(0x40000000)) as double < float64_from_bits(0x4030000000000000u64)"
        );
        let integer = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::uint64_constant(1.5_f64.to_bits())),
                right: Box::new(OldMachineTerm::Variable(Variable(9))),
            },
            true,
        );
        assert!(source(&integer, &mut labels).contains("4609434218613702656u64"));
    }

    #[test]
    fn named_pure_function_facts_keep_their_surface_arguments() {
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(7), "r".into());
        let application = crate::kernel::SharedPureApplication::intern(
            "size".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                OldMachineTerm::Variable(Variable(7)),
            ))],
        );
        let fact = Proposition::Equal(
            Term::Integer(IntegerTerm::PureFunctionApplication(application).into()),
            Term::Integer(IntegerTerm::from(3).into()),
        );
        assert_eq!(render(&fact, &mut labels), Some("size(r) == 3".into()));
    }

    #[test]
    fn unnamed_operands_keep_their_context_without_becoming_exact_citations() {
        let mut labels = MemoryStateLabels::default();
        for depth in [0, 16, 64, 256] {
            let mut term = OldMachineTerm::Variable(Variable(999));
            for _ in 0..depth {
                term = binary_node!(
                    Int32,
                    Add,
                    Box::new(term),
                    Box::new(OldMachineTerm::constant(1))
                );
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
        let mut labels = MemoryStateLabels::default();
        let first = equality(OldMachineTerm::Variable(Variable(998)));
        let second = equality(OldMachineTerm::Variable(Variable(999)));
        assert_eq!(source(&first, &mut labels), "<unnamed A> == 0");
        assert_eq!(source(&second, &mut labels), "<unnamed B> == 0");
        assert_eq!(source(&first, &mut labels), "<unnamed A> == 0");
        assert!(render(&first, &mut labels).is_none());
    }

    /// A contract's entry model is spelled `old(owner.field)`, which always
    /// denotes it. A model a call replaced has no point-free spelling and keeps
    /// its placeholder.
    #[test]
    fn a_contract_entry_model_field_is_spelled_with_old() {
        use crate::kernel::model_fields::{ModelFieldOrigin, ModelMint};
        let _session = crate::kernel::VerificationSession::enter();
        let instance = crate::kernel::InstanceId::from_variable(Variable(901_000));
        let register = |variable, minted_by| {
            crate::kernel::model_fields::register_model_field_variable(
                Variable(variable),
                ModelFieldOrigin {
                    identity: instance,
                    field: "count".into(),
                    field_index: 0,
                    minted_by,
                },
            )
        };
        register(901_001, ModelMint::ContractEntry { owner: "up".into() });
        register(
            901_002,
            ModelMint::CallReturn {
                callee: "refill".into(),
            },
        );
        let mut labels = MemoryStateLabels::default();
        let entry = equality(OldMachineTerm::Variable(Variable(901_001)));
        let replaced = equality(OldMachineTerm::Variable(Variable(901_002)));
        assert_eq!(source(&entry, &mut labels), "old(up.count) == 0");
        assert_eq!(source(&replaced, &mut labels), "<unnamed A> == 0");
    }

    #[test]
    fn narrowed_wide_values_keep_the_signed_comparison_view() {
        let state = ExecutionState::new().with_local(
            "size",
            ProgramValue::UInt64(OldMachineTerm::Variable(Variable(94))),
        );
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &state);
        let value = OldMachineTerm::legacy_cast(
            MachineCastSpelling::UInt32From64,
            Box::new(OldMachineTerm::Variable(Variable(94))),
        );
        let fact = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(value),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        );
        assert_eq!(
            render(&fact, &mut labels).unwrap(),
            "size as uint32 as int32 < 0"
        );
        assert_eq!(source(&fact, &mut labels), "size as uint32 as int32 < 0");
    }

    #[test]
    fn source_constants_print_in_the_type_of_their_comparison() {
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(7), "a".into());
        labels.source_name(Variable(8), "u".into());
        labels.source_types.insert(Variable(8), ProgramType::UInt32);
        let signed = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(7))),
                right: Box::new(OldMachineTerm::constant((-56i32) as u32)),
            },
            true,
        );
        assert_eq!(source(&signed, &mut labels), "a == -56");
        let unsigned = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(8))),
                right: Box::new(OldMachineTerm::constant((-56i32) as u32)),
            },
            false,
        );
        assert_eq!(source(&unsigned, &mut labels), "u != 4294967240u32");
        // An unsigned order over an `int32` value converts it.
        let order = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation: CompareRelation::LessEqual,
                left: Box::new(OldMachineTerm::Variable(Variable(7))),
                right: Box::new(OldMachineTerm::constant(1073741823)),
            },
            true,
        );
        assert_eq!(source(&order, &mut labels), "a as uint32 <= 1073741823u32");
    }

    #[test]
    fn machine_arithmetic_comparisons_preserve_their_observations() {
        for (format, source_type) in [
            (MachineIntegerType::Int32, ProgramType::Int32),
            (MachineIntegerType::UInt32, ProgramType::UInt32),
            (MachineIntegerType::Int64, ProgramType::Int64),
            (MachineIntegerType::UInt64, ProgramType::UInt64),
        ] {
            let mut labels = MemoryStateLabels::default();
            labels.source_name(Variable(7), "a".into());
            labels.source_name(Variable(8), "b".into());
            labels.source_types.insert(Variable(7), source_type);
            labels.source_types.insert(Variable(8), source_type);
            for (op, symbol) in [
                (MachineBinaryOp::Add, "+"),
                (MachineBinaryOp::Subtract, "-"),
                (MachineBinaryOp::Multiply, "*"),
            ] {
                let arithmetic = OldMachineTerm::Binary {
                    format: if format == MachineIntegerType::UInt32 {
                        MachineIntegerType::Int32
                    } else {
                        format
                    },
                    op,
                    left: Box::new(OldMachineTerm::Variable(Variable(7))),
                    right: Box::new(OldMachineTerm::Variable(Variable(8))),
                };
                let fact = Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format,
                        relation: CompareRelation::LessThan,
                        left: Box::new(arithmetic.clone()),
                        right: Box::new(arithmetic),
                    },
                    false,
                );
                let expected = format!("to_integer(a {symbol} b) >= to_integer(a {symbol} b)");
                assert_eq!(source(&fact, &mut labels), expected);
                if format == MachineIntegerType::Int32 {
                    assert_eq!(render(&fact, &mut labels).unwrap(), expected);
                }
            }
        }
    }

    #[test]
    fn source_spelling_uses_minimal_parentheses_and_click_connectives() {
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(7), "a".into());
        labels.source_name(Variable(8), "b".into());
        let a = || Box::new(OldMachineTerm::Variable(Variable(7)));
        let b = || Box::new(OldMachineTerm::Variable(Variable(8)));
        let product = binary_node!(
            Int32,
            Multiply,
            Box::new(binary_node!(Int32, Add, a(), b())),
            Box::new(binary_node!(Int32, Subtract, a(), b())),
        );
        let less = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(product),
                right: a(),
            },
            false,
        );
        let masked = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(binary_node!(Int32, BitwiseAnd, a(), b())),
                right: Box::new(OldMachineTerm::constant(0)),
            },
            true,
        );
        let fact = Proposition::Implies(
            Box::new(Proposition::And(Box::new(less), Box::new(masked.clone()))),
            Box::new(Proposition::Not(Box::new(masked))),
        );
        assert_eq!(
            source(&fact, &mut labels),
            "to_integer((a + b) * (a - b)) >= a and (a & b) == 0 implies not ((a & b) == 0)"
        );
    }

    #[test]
    fn definedness_distinguishes_points_with_identical_memory() {
        use crate::surface::{ProgramPointSelector, RecordedStates};

        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::symbolic(Variable(7));
        let pointer_value =
            ProgramValue::Pointer(Pointer::new(pointer.clone(), ProgramType::Int32Pointer));
        let before = ExecutionState::new()
            .with_local("before_ptr", pointer_value.clone())
            .with_memory(SymbolicMemory::new());
        let current = ExecutionState::new()
            .with_local("current_ptr", pointer_value)
            .with_memory(before.memory().clone());
        assert!(before.memory().same_storage_roots(current.memory()));
        assert!(before.observation_point_id().is_some());
        assert!(current.observation_point_id().is_some());
        assert_ne!(
            before.observation_point_id(),
            current.observation_point_id()
        );

        let mut recorded = RecordedStates::new();
        recorded.insert(ProgramPointSelector::Mark("before".into()), before.clone());
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &current);
        labels.recorded_states(&recorded);
        let defined_at = |state: &ExecutionState| Proposition::MemoryReadDefined {
            point: Default::default(),
            at: state.observation_point_id(),
            memory: before.memory().clone(),
            pointer: pointer.clone(),
            value_type: ProgramType::Int32,
        };
        let historical = source(&defined_at(&before), &mut labels);
        assert!(
            historical.starts_with("at(before, defined("),
            "{historical}"
        );
        assert!(historical.contains("before_ptr"), "{historical}");
        let now = source(&defined_at(&current), &mut labels);
        assert!(now.starts_with("defined("), "{now}");
        assert!(now.contains("current_ptr"), "{now}");
    }

    #[test]
    fn predicate_array_arguments_keep_their_individual_states() {
        let pointer = ProgramValue::Pointer(Pointer::new(
            Address::new(
                AddressBase::Concrete("global:cells".into()),
                AddressOffset::constant(0),
            ),
            ProgramType::Int32Pointer,
        ));
        let before = ExecutionState::new()
            .with_local("cells", pointer.clone())
            .with_memory(SymbolicMemory::new().with_block("global:cells", 4));
        let copied = before
            .clone()
            .with_memory(SymbolicMemory::new().with_block("global:cells", 8));
        let current = before
            .clone()
            .with_memory(SymbolicMemory::new().with_block("global:cells", 16));
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &current);
        labels.source_state(&before, ENTRY_POINT.into());
        labels.source_state(&copied, "copied".into());
        let predicate = |memories: [&SymbolicMemory; 3]| Proposition::Predicate {
            name: "same".into(),
            arguments: std::iter::once(Term::ExecutionState(Box::new(before.clone())))
                .chain(memories.into_iter().flat_map(|memory| {
                    [
                        Term::ArrayReadPoint(crate::kernel::ProgramPoint::of_memory(memory)),
                        Term::ProgramValue(pointer.clone().into()),
                    ]
                }))
                .collect(),
        };
        assert_eq!(
            source(
                &predicate([before.memory(), copied.memory(), current.memory()]),
                &mut labels,
            ),
            "same(old(cells), at(copied, cells), cells)"
        );
        let fact = predicate([current.memory(); 3]);
        assert_eq!(source(&fact, &mut labels), "same(cells, cells, cells)");
        assert_eq!(source(&fact, &mut labels), "same(cells, cells, cells)");
    }

    #[test]
    fn reserved_predicates_print_the_click_spelling_that_lowers_to_them() {
        let cell = |name: &str| {
            ProgramValue::Pointer(Pointer::new(
                Address::new(
                    AddressBase::Concrete(format!("global:{name}")),
                    AddressOffset::constant(0),
                ),
                ProgramType::Int32Pointer,
            ))
        };
        let state = ExecutionState::new()
            .with_local("m", cell("m"))
            .with_local("p", cell("p"))
            .with_memory(SymbolicMemory::new().with_block("global:m", 4));
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &state);
        let fact = |name: String, arguments: Vec<Term>| Proposition::Predicate { name, arguments };
        let same = fact(
            crate::kernel::SAME_ALLOCATION_PREDICATE_NAME.into(),
            vec![
                Term::ProgramValue((cell("m")).into()),
                Term::ProgramValue((cell("p")).into()),
            ],
        );
        assert_eq!(source(&same, &mut labels), "same_allocation(m, p)");
        let contract = fact(
            crate::kernel::FunctionContract::predicate_name_for("ordered"),
            vec![
                Term::ExecutionState(Box::new(state.clone())),
                Term::ProgramValue((cell("p")).into()),
            ],
        );
        assert_eq!(source(&contract, &mut labels), "ordered(p)");
        for (premise, internal) in [(&same, false), (&contract, false)] {
            assert_eq!(
                crate::surface::proof_diagnostics::is_internal_premise(premise),
                internal
            );
        }
        let covers = fact(
            format!("{}4", crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX),
            vec![],
        );
        assert!(crate::surface::proof_diagnostics::is_internal_premise(
            &covers
        ));
        let composition = Proposition::ResourceComposition(crate::kernel::ResourceContext::new());
        assert!(crate::surface::proof_diagnostics::is_internal_premise(
            &composition
        ));
    }

    #[test]
    fn the_contract_result_local_prints_as_result() {
        let state = ExecutionState::new().with_local(
            crate::kernel::CONTRACT_RESULT,
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(7))),
        );
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &state);
        assert_eq!(
            source(
                &equality(OldMachineTerm::Variable(Variable(7))),
                &mut labels
            ),
            "result == 0"
        );
    }

    #[test]
    fn historical_loads_use_their_own_state_names_and_keep_their_read_type() {
        let pointer = Address::new(
            AddressBase::Concrete("global:cells".into()),
            AddressOffset::constant(0),
        );
        let base = ProgramValue::Pointer(Pointer::new(pointer.clone(), ProgramType::Int32Pointer));
        let before = ExecutionState::new()
            .with_local("cells", base.clone())
            .with_memory(SymbolicMemory::new().with_block("global:cells", 4));
        let after = before
            .clone()
            .with_memory(SymbolicMemory::new().with_block("global:cells", 8));
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &after);
        labels.source_state(&before, "pre".into());
        let load = |memory: &SymbolicMemory, kind| {
            equality(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&(SharedMemory::from(memory.clone()))),
                Box::new(pointer.clone()),
                kind,
            ))
        };
        assert_eq!(
            render(&load(before.memory(), LoadKind::Int32), &mut labels),
            Some("at(pre, cells[0]) == 0".into())
        );
        assert_eq!(
            render(&load(after.memory(), LoadKind::Int32), &mut labels),
            Some("cells[0] == 0".into())
        );
        assert_eq!(
            render(&load(before.memory(), LoadKind::UInt8), &mut labels),
            None
        );
        let unknown = SymbolicMemory::new().with_block("global:cells", 16);
        assert_eq!(render(&load(&unknown, LoadKind::Int32), &mut labels), None);
        // The source policy names the unknown memory instead of refusing, so
        // the two reads of `cells[0]` stay distinct.
        assert_eq!(
            source(&load(&unknown, LoadKind::Int32), &mut labels),
            "at(<state A>, cells[0]) == 0"
        );
        assert_eq!(
            source(&load(after.memory(), LoadKind::Int32), &mut labels),
            "cells[0] == 0"
        );
        assert!(labels.trace_legend().contains("<state A> is "));
    }

    #[test]
    fn result_names_the_returned_value_only_where_result_exists() {
        let index = Variable(9);
        let heap = Address::new(AddressBase::Heap(1), AddressOffset::constant(0));
        let before =
            ExecutionState::new().with_memory(SymbolicMemory::new().with_block("global:a", 4));
        let after =
            ExecutionState::new().with_memory(SymbolicMemory::new().with_block("global:a", 8));
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &after);
        labels.source_state(&before, "pre".into());
        labels.source_result(&ProgramValue::Int32(OldMachineTerm::Variable(index)));
        // An allocation no local holds is the returned pointer.
        labels.source_result(&ProgramValue::Pointer(Pointer::new(
            heap.clone(),
            ProgramType::Int32Pointer,
        )));
        let load = |memory: &SymbolicMemory| {
            equality(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&(SharedMemory::from(memory.clone()))),
                Box::new(heap.clone()),
                LoadKind::Int32,
            ))
        };
        assert_eq!(
            source(&equality(OldMachineTerm::Variable(index)), &mut labels),
            "result == 0"
        );
        assert_eq!(source(&load(after.memory()), &mut labels), "*result == 0");
        // `result` does not exist at `pre`, so a read there is not spelled
        // through it.
        assert_eq!(
            source(&load(before.memory()), &mut labels),
            "at(pre, *<pointer A>) == 0"
        );
    }

    #[test]
    fn reassigned_parameters_do_not_rename_their_old_value_as_current() {
        let entry = ExecutionState::new().with_local(
            "i",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(7))),
        );
        let current = entry.clone().with_local(
            "i",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(8))),
        );
        let (names, values) = crate::surface::diagnostics::local_naming_tables(&entry);
        let mut labels =
            MemoryStateLabels::with_state(ParameterBinding::new(&names, &values), &current);
        assert_eq!(
            render(
                &equality(OldMachineTerm::Variable(Variable(7))),
                &mut labels
            ),
            Some("old(i) == 0".into())
        );
        assert_eq!(
            render(
                &equality(OldMachineTerm::Variable(Variable(8))),
                &mut labels
            ),
            Some("i == 0".into())
        );
    }
}

/// The name in `naming` that holds a slice whose count is `count`, with the
/// slice's element.
fn counted_slice_name(
    count: &OldMachineTerm,
    naming: &NamingTables,
) -> Option<(String, crate::kernel::SliceElement)> {
    naming
        .0
        .iter()
        .zip(&naming.1)
        .find_map(|(name, value)| match value {
            crate::kernel::ProgramExpression::Value(crate::kernel::ProgramValue::Pointer(held))
                if held.is_wide() && held.len() == Some(count) && name.name().len() <= 256 =>
            {
                let crate::kernel::ProgramType::SlicePointer(element) = held.program_type() else {
                    return None;
                };
                Some((name.name().to_owned(), element))
            }
            _ => None,
        })
}

#[cfg(test)]
mod resource_tests {
    use super::*;
    use crate::kernel::{
        AddressBase, AlgebraicType, ExecutionState, LoadKind, Pointer, ProgramType, ProgramValue,
        SharedMemory,
    };

    #[test]
    fn resource_arguments_keep_the_same_read_states_as_proposition_operands() {
        let pointer = Address::new(
            AddressBase::Concrete("global:cells".into()),
            AddressOffset::constant(0),
        );
        let before = ExecutionState::new()
            .with_local(
                "cells",
                ProgramValue::Pointer(Pointer::new(pointer.clone(), ProgramType::Int32Pointer)),
            )
            .with_memory(SymbolicMemory::new().with_block("global:cells", 4));
        let after = before
            .clone()
            .with_memory(SymbolicMemory::new().with_block("global:cells", 8));
        let resource = |memory: &SymbolicMemory| {
            ResourceFact::view_composite(
                "sampled".into(),
                vec![ProgramValue::Int32(OldMachineTerm::read_named(
                    crate::kernel::ProgramPoint::at(&(SharedMemory::from(memory.clone()))),
                    Box::new(pointer.clone()),
                    LoadKind::Int32,
                ))],
            )
        };
        let mut labels = MemoryStateLabels::with_state(ParameterBinding::default(), &after);
        labels.source_state(&before, "pre".into());
        assert_eq!(
            source_resource_fact(&resource(before.memory()), &mut labels),
            "views sampled(at(pre, cells[0]))"
        );
        assert_eq!(
            source_resource_fact(&resource(after.memory()), &mut labels),
            "views sampled(cells[0])"
        );
        let separate = Proposition::ResourceSeparate {
            left: Box::new(resource(before.memory()).resource().clone()),
            right: Box::new(resource(after.memory()).resource().clone()),
        };
        assert_eq!(
            source(&separate, &mut labels),
            "separate(sampled(at(pre, cells[0])), sampled(cells[0]))"
        );
        let list = super::super::render_resource_facts_diagnostic(
            &[resource(before.memory()), resource(after.memory())],
            ParameterBinding::default(),
        );
        assert!(
            list.contains("at(<state A>,") && list.contains("at(<state B>,"),
            "{list}"
        );
        assert_eq!(list.matches("\n  where").count(), 1, "{list}");
    }

    #[test]
    fn resource_model_arguments_remain_distinct_and_quantities_survive() {
        let resource = |id| Resource::Token {
            name: "tree".into(),
            arguments: vec![AlgebraicValue::Algebraic(AlgebraicTerm {
                algebraic_type: AlgebraicType::parameter("Tree".into()),
                node: AlgebraicTermNode::Variable(Variable(id)),
            })]
            .into(),
        };
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(987551), "left_model".into());
        labels.source_name(Variable(987552), "right_model".into());
        let left = ResourceFact::own_quantity(resource(987551), OldMachineTerm::constant(2));
        let right = ResourceFact::View(resource(987552));
        assert_eq!(
            source_resource_fact(&left, &mut labels),
            "owns tree(left_model) (quantity 2)"
        );
        assert_eq!(
            source_resource_fact(&right, &mut labels),
            "views tree(right_model)"
        );
        assert_eq!(
            source(
                &Proposition::ResourceSeparate {
                    left: Box::new(left.resource().clone()),
                    right: Box::new(right.resource().clone())
                },
                &mut labels
            ),
            "separate(tree(left_model), tree(right_model))"
        );
    }
}

/// A match from its spelled scrutinee and arms. A single tuple arm whose
/// body is one of its bindings, `(_0, _1) => _1`, is the projection `t.1`
/// it lowers from (`design/tuples.md`).
fn tuple_match_spelling(scrutinee: &str, arm_count: usize, arms: &[String]) -> String {
    if arm_count == 1
        && let [arm] = arms
        && let Some((pattern, body)) = arm.split_once(" => ")
        && let Some(inner) = pattern.strip_prefix('(').and_then(|p| p.strip_suffix(')'))
        && !inner.contains(['(', ')'])
    {
        let bindings = inner
            .split(',')
            .map(str::trim)
            .filter(|binding| !binding.is_empty())
            .collect::<Vec<_>>();
        if let Some(index) = bindings.iter().rposition(|binding| *binding == body)
            && *bindings[index] != *"_"
        {
            return crate::surface::tuples::spell_projection(scrutinee, index);
        }
    }
    format!("match {scrutinee} {{ {} }}", arms.join(", "))
}
