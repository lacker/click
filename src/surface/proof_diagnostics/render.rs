//! A bounded renderer for kernel propositions used in proof failure reports.
//!
//! This deliberately has its own small printer.  `Debug` for a proposition is
//! useful to developers, but it is an implementation dump: it can repeat a
//! shared DAG, include whole memory snapshots, and grow without relation to
//! the useful part of a diagnostic.

use crate::kernel::{
    AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, Bitvector32Term, CExpressionOutcome, CMemory,
    CResource, CState, ConditionTerm, IntegerRangeFoldIndex, IntegerTerm, Pointer,
    PointerOffsetTerm, Proposition, PureFunctionArgument, SpecCaptureRefusal, Term,
};
use std::fmt::Write;

const MAX_BYTES: usize = 32 * 1024;
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 96;
/// How many distinct snapshots one report labels before it stops comparing.
/// A message names a handful of states; the cap keeps the comparison below
/// bounded, and a snapshot past it simply gets its own label.
const MAX_SNAPSHOT_LABELS: usize = 32;

/// The snapshot labels of one report.
///
/// A snapshot used to print the addresses of the five `Arc` roots it is built
/// from, so two structurally identical memories printed as different tuples
/// and a reader could not tell "same memory" from "different memory" — the one
/// thing those labels exist to show. A label is now a small ordinal, assigned
/// in order of first appearance and shared by equal memories, so `snapshot#1`
/// twice means one memory and `snapshot#1`/`snapshot#2` means two.
#[derive(Default)]
pub(crate) struct SnapshotLabels {
    memories: Vec<CMemory>,
}

impl SnapshotLabels {
    /// The label of this memory: an existing ordinal when an equal memory has
    /// already been labeled, otherwise the next one.
    fn label(&mut self, memory: &CMemory) -> usize {
        if let Some(index) = self
            .memories
            .iter()
            .position(|labeled| labeled.same_storage_roots(memory) || labeled == memory)
        {
            return index + 1;
        }
        if self.memories.len() >= MAX_SNAPSHOT_LABELS {
            return self.memories.len() + 1;
        }
        self.memories.push(memory.clone());
        self.memories.len()
    }
}

/// Render one proposition without allowing its shape or attached snapshots to
/// determine the size of the error message.
pub(crate) fn render_proposition(proposition: &Proposition) -> String {
    render_proposition_labeled(proposition, &mut SnapshotLabels::default())
}

/// [`render_proposition`] sharing one report's snapshot labels, so the same
/// memory reads as the same `snapshot#n` in every line of that report.
pub(crate) fn render_proposition_labeled(
    proposition: &Proposition,
    labels: &mut SnapshotLabels,
) -> String {
    let mut renderer = Renderer {
        output: String::with_capacity(1024),
        nodes: 0,
        depth: 0,
        truncated: false,
        labels,
    };
    renderer.proposition(proposition);
    if renderer.truncated {
        const SUFFIX: &str = "\n… <proof proposition truncated>";
        let limit = MAX_BYTES.saturating_sub(SUFFIX.len());
        let mut end = limit.min(renderer.output.len());
        while end > 0 && !renderer.output.is_char_boundary(end) {
            end -= 1;
        }
        renderer.output.truncate(end);
        renderer.output.push_str(SUFFIX);
    }
    renderer.output
}

/// Render one exact-arithmetic term under the same bounds.
///
/// An `IntegerTerm` can hold a pure-function application or an algebraic
/// elimination, so its `Debug` reaches the same datatype schemas a
/// proposition's does.
pub(crate) fn render_integer_term(term: &IntegerTerm) -> String {
    let mut labels = SnapshotLabels::default();
    let mut renderer = Renderer {
        output: String::with_capacity(128),
        nodes: 0,
        depth: 0,
        truncated: false,
        labels: &mut labels,
    };
    renderer.integer(term);
    if renderer.truncated {
        renderer.output.push('…');
    }
    renderer.output
}

/// Describe a refused Integer capture: which written subterm carries an
/// evaluation condition, and which condition the proof context is missing.
pub(crate) fn describe_spec_capture_refusal(refusal: &SpecCaptureRefusal) -> String {
    match refusal {
        SpecCaptureRefusal::Message(message) => message.clone(),
        SpecCaptureRefusal::Undischarged {
            subterm,
            proposition,
        } => format!(
            "{} denotes this value only where `{}` holds, and that is not available here",
            subterm.describe(),
            render_proposition(proposition)
        ),
    }
}

struct Renderer<'a> {
    output: String,
    nodes: usize,
    depth: usize,
    truncated: bool,
    labels: &'a mut SnapshotLabels,
}

impl Renderer<'_> {
    fn fmt(&mut self, arguments: std::fmt::Arguments<'_>) {
        struct Sink<'a, 'b>(&'a mut Renderer<'b>);
        impl std::fmt::Write for Sink<'_, '_> {
            fn write_str(&mut self, value: &str) -> std::fmt::Result {
                self.0.push(value);
                if self.0.truncated {
                    Err(std::fmt::Error)
                } else {
                    Ok(())
                }
            }
        }
        let _ = Sink(self).write_fmt(arguments);
    }
    fn push(&mut self, text: &str) {
        if self.truncated {
            return;
        }
        let remaining = MAX_BYTES.saturating_sub(self.output.len());
        if text.len() <= remaining {
            self.output.push_str(text);
            return;
        }
        let mut end = remaining.min(text.len());
        while end > 0 && !text.is_char_boundary(end) {
            end -= 1;
        }
        self.output.push_str(&text[..end]);
        self.truncated = true;
    }

    fn visit(&mut self) -> bool {
        if self.truncated {
            return false;
        }
        self.nodes = self.nodes.saturating_add(1);
        if self.nodes > MAX_NODES || self.depth >= MAX_DEPTH {
            self.truncated = true;
            self.push("…");
            return false;
        }
        true
    }

    fn proposition(&mut self, proposition: &Proposition) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match proposition {
            Proposition::Equal(left, right) => self.binary_term(left, " = ", right),
            Proposition::ConditionIs(condition, value) => {
                self.condition(condition);
                self.push(if *value { " is true" } else { " is false" });
            }
            Proposition::Predicate { name, arguments } => {
                self.push("predicate ");
                self.push(name);
                self.push("(");
                self.terms(arguments);
                self.push(")");
            }
            Proposition::And(left, right) => self.binary_prop(left, " ∧ ", right),
            Proposition::Or(left, right) => self.binary_prop(left, " ∨ ", right),
            Proposition::Implies(left, right) => self.binary_prop(left, " ⇒ ", right),
            Proposition::Not(body) => {
                self.push("¬(");
                self.proposition(body);
                self.push(")");
            }
            Proposition::ForAll { var, sort, body } => {
                self.fmt(format_args!("∀v{}:{sort:?}. ", var.0));
                self.proposition(body);
            }
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } => {
                self.fmt(format_args!("∃{name}/v{}:{sort:?}. ", var.0));
                self.proposition(body);
            }
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
            } => {
                self.push("viewable(memory=");
                self.memory(memory);
                self.push(", base=");
                self.pointer(base);
                self.push(", bytes=");
                self.bitvector(bytes);
                self.push(")");
            }
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => {
                self.push("can-store(memory=");
                self.memory(memory);
                self.push(", pointer=");
                self.pointer(pointer);
                self.fmt(format_args!(", bytes={byte_width})"));
            }
            Proposition::CMemoryLoads {
                memory,
                pointer,
                outcome,
            } => {
                self.push("memory-load(memory=");
                self.memory(memory);
                self.push(", pointer=");
                self.pointer(pointer);
                self.push(", outcome=");
                self.outcome(outcome);
                self.push(")");
            }
            Proposition::CResourceSeparate { left, right } => {
                self.resource(left);
                self.push(" separate ");
                self.resource(right);
            }
            Proposition::CResourceContains { parent, child } => {
                self.resource(parent);
                self.push(" contains ");
                self.resource(child);
            }
            Proposition::CResourceComposition(_) => {
                self.push("resource-composition(<validated resource context>)")
            }
            Proposition::CMemoryMutatesOnly {
                before,
                after,
                writes,
            } => {
                self.push("memory-mutates-only(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                self.push(", writes=");
                for (index, (pointer, bytes)) in writes.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.pointer(pointer);
                    self.push(&format!(" ({bytes} bytes)"));
                }
                self.push(")");
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                self.push("memory-effects(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                self.fmt(format_args!(", ranges={})", mutable_ranges.len()));
            }
            Proposition::CHeapAllocationFreed {
                before,
                after,
                allocation_base,
                bytes,
            } => {
                self.push("heap-freed(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                self.push(", base=");
                self.pointer(allocation_base);
                self.push(", bytes=");
                self.bitvector(bytes);
                self.push(")");
            }
            Proposition::CExpressionEvaluates {
                state,
                expression: _,
                outcome,
            } => {
                self.push("expression-evaluates(state=");
                self.state(state);
                self.push(", expression=<C expression>, outcome=");
                self.outcome(outcome);
                self.push(")");
            }
            Proposition::CConditionEvaluates {
                state,
                condition: _,
                outcome,
            } => {
                self.push("condition-evaluates(state=");
                self.state(state);
                self.push(", condition=<C condition>, outcome=");
                self.condition_outcome(outcome);
                self.push(")");
            }
            Proposition::CStatementExecutes {
                state,
                statement: _,
                outcome,
            }
            | Proposition::CStatementVerifies {
                state,
                statement: _,
                outcome,
            } => {
                self.push("statement-");
                self.push(
                    if matches!(proposition, Proposition::CStatementVerifies { .. }) {
                        "verifies"
                    } else {
                        "executes"
                    },
                );
                self.push("(state=");
                self.state(state);
                self.push(", statement=<C statement>, outcome=");
                self.statement_outcome(outcome);
                self.push(")");
            }
            Proposition::CFunctionExecutes {
                state,
                function: _,
                arguments,
                outcome,
            }
            | Proposition::CFunctionVerifies {
                state,
                function: _,
                arguments,
                outcome,
            } => {
                self.push("function-call(state=");
                self.state(state);
                self.fmt(format_args!(
                    ", function=<C function>, args={}, outcome=",
                    arguments.len()
                ));
                self.function_outcome(outcome);
                self.push(")");
            }
            Proposition::CFunctionSatisfiesSpecification { .. } => {
                self.push("function-satisfies(<C function specification>)")
            }
            Proposition::CFunctionPartiallySatisfiesSpecification { .. } => {
                self.push("function-partially-satisfies(<C function specification>)")
            }
        }
        self.depth -= 1;
    }

    fn binary_prop(&mut self, left: &Proposition, op: &str, right: &Proposition) {
        self.push("(");
        self.proposition(left);
        self.push(op);
        self.proposition(right);
        self.push(")");
    }
    fn binary_term(&mut self, left: &Term, op: &str, right: &Term) {
        self.term(left);
        self.push(op);
        self.term(right);
    }
    fn terms(&mut self, terms: &[Term]) {
        for (index, term) in terms.iter().enumerate() {
            if self.truncated {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.term(term);
        }
    }
    fn term(&mut self, term: &Term) {
        if !self.visit() {
            return;
        }
        match term {
            Term::Condition(c) => self.condition(c),
            Term::Bitvector32(v) => self.bitvector(v),
            Term::Integer(i) => self.integer(i),
            Term::PointerOffset(o) => self.offset(o, 0),
            Term::CValue(v) => self.cvalue(v),
            Term::CExpressionOutcome(o) => self.outcome(o),
            Term::CStatementOutcome(_) => self.push("statement-outcome(<state snapshot>)"),
            Term::CFunctionOutcome(_) => self.push("function-outcome(<state snapshot>)"),
            Term::CMemory(m) => self.memory(m),
            Term::CState(s) => self.state(s),
            Term::Sequence(_) => self.push("sequence(<bounded opaque value>)"),
            Term::Algebraic(value) => self.algebraic(value),
        }
    }

    /// Renders an algebraic term in its source spelling: a constructor, a pure
    /// function application, an elimination, or a binder.
    ///
    /// The datatype's declaration graph is deliberately not rendered. An
    /// `AlgebraicTerm` carries the whole instantiated `AlgebraicSchemas` so the
    /// kernel can check formation without trusting surface names, and printing
    /// that structure repeats every variant of every reachable family for each
    /// occurrence of a value. The type's own name is what a reader needs.
    fn algebraic(&mut self, term: &AlgebraicTerm) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match &term.node {
            AlgebraicTermNode::Variable(variable) => {
                self.fmt(format_args!("v{}:{}", variable.0, term.algebraic_type.name))
            }
            AlgebraicTermNode::Constructor { variant, fields } => {
                self.fmt(format_args!("{}::{variant}", term.algebraic_type.name));
                if !fields.is_empty() {
                    self.push("(");
                    for (index, field) in fields.iter().enumerate() {
                        if self.truncated {
                            break;
                        }
                        if index > 0 {
                            self.push(", ");
                        }
                        self.algebraic_value(field);
                    }
                    self.push(")");
                }
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                self.push("match ");
                self.algebraic(scrutinee);
                self.push(" { ");
                for (index, arm) in arms.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&arm.variant);
                    self.push(" => ");
                    self.algebraic(&arm.body);
                }
                self.push(" }");
            }
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                self.pure_arguments(arguments);
                self.push(")");
            }
        }
        self.depth -= 1;
    }

    fn algebraic_value(&mut self, value: &AlgebraicValue) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match value {
            AlgebraicValue::C(value) => self.cvalue(value),
            AlgebraicValue::Integer(value) => self.integer(value),
            AlgebraicValue::Algebraic(value) => self.algebraic(value),
        }
        self.depth -= 1;
    }

    fn pure_arguments(&mut self, arguments: &[PureFunctionArgument]) {
        for (index, argument) in arguments.iter().enumerate() {
            if self.truncated {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.pure_argument(argument);
        }
    }

    fn pure_argument(&mut self, argument: &PureFunctionArgument) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match argument {
            PureFunctionArgument::Value(value) => self.cvalue(value),
            PureFunctionArgument::Integer(value) => self.integer_shared(value),
            PureFunctionArgument::Algebraic(value) => self.algebraic(value),
            // The snapshot identity is printed, not elided. A goal that
            // compares the same pure function at two states -- a loop
            // invariant about a sequence, or a ranking measure's pre and post
            // -- differs only in this argument's memory, so eliding it
            // rendered `count(a) < count(a)`: a reader could not tell the two
            // sides apart, and a true goal read as a false one.
            PureFunctionArgument::ArrayRef {
                memory, pointer, ..
            } => {
                self.push("array-ref(");
                self.memory(memory);
                self.push(", ");
                self.cvalue(pointer);
                self.push(")");
            }
        }
        self.depth -= 1;
    }
    fn condition(&mut self, c: &ConditionTerm) {
        match c {
            ConditionTerm::Constant(v) => self.push(if *v { "true" } else { "false" }),
            ConditionTerm::Variable(v) => self.fmt(format_args!("condition-v{}", v.0)),
            ConditionTerm::IntegerLessThan(a, b)
            | ConditionTerm::IntegerLessEqual(a, b)
            | ConditionTerm::IntegerGreaterThan(a, b)
            | ConditionTerm::IntegerGreaterEqual(a, b)
            | ConditionTerm::IntegerEqual(a, b)
            | ConditionTerm::IntegerNotEqual(a, b) => {
                self.push("integer-condition(");
                self.integer_shared(a);
                self.push(match c {
                    ConditionTerm::IntegerLessThan(..) => " < ",
                    ConditionTerm::IntegerLessEqual(..) => " <= ",
                    ConditionTerm::IntegerGreaterThan(..) => " > ",
                    ConditionTerm::IntegerGreaterEqual(..) => " >= ",
                    ConditionTerm::IntegerEqual(..) => " = ",
                    _ => " != ",
                });
                self.integer_shared(b);
                self.push(")");
            }
            ConditionTerm::Bitvector32SignedLessThan(a, b) => {
                self.binary_condition_bv(a, b, "int32 <")
            }
            ConditionTerm::Bitvector32SignedLessEqual(a, b) => {
                self.binary_condition_bv(a, b, "int32 <=")
            }
            ConditionTerm::Bitvector32SignedGreaterThan(a, b) => {
                self.binary_condition_bv(a, b, "int32 >")
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(a, b) => {
                self.binary_condition_bv(a, b, "int32 >=")
            }
            ConditionTerm::Bitvector32Equal(a, b) => self.binary_condition_bv(a, b, "int32 ="),
            ConditionTerm::AlgebraicEqual(a, b) => {
                self.algebraic(a);
                self.push(" = ");
                self.algebraic(b);
            }
            ConditionTerm::PointerOffsetEqual(a, b) => {
                self.offset(a, 0);
                self.push(" = ");
                self.offset(b, 0);
            }
            ConditionTerm::PointerEqual(a, b) => {
                self.pointer(a);
                self.push(" = ");
                self.pointer(b);
            }
            // Definedness of a partial machine operation is the condition a
            // capture or evaluation refusal most often names, so print the
            // operation instead of a placeholder.
            ConditionTerm::Bitvector32SignedAddOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "+")
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "-")
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "*")
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "/")
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "<<")
            }
            ConditionTerm::Bitvector64SignedAddOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "+")
            }
            ConditionTerm::Bitvector64SignedSubtractOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "-")
            }
            ConditionTerm::Bitvector64SignedMultiplyOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "*")
            }
            ConditionTerm::Bitvector64SignedDivideOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "/")
            }
            ConditionTerm::Bitvector64SignedShiftLeftOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "<<")
            }
            _ => self.push("condition(<bounded operation>)"),
        }
    }
    fn binary_condition_bv(&mut self, a: &Bitvector32Term, b: &Bitvector32Term, label: &str) {
        self.push(label);
        self.push("(");
        self.bitvector(a);
        self.push(", ");
        self.bitvector(b);
        self.push(")");
    }
    fn overflow_condition_bv(
        &mut self,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
        width: &str,
        operator: &str,
    ) {
        self.push(width);
        self.push(" overflow(");
        self.bitvector(a);
        self.push(" ");
        self.push(operator);
        self.push(" ");
        self.bitvector(b);
        self.push(")");
    }
    fn integer(&mut self, i: &IntegerTerm) {
        if self.truncated {
            return;
        }
        match i {
            IntegerTerm::Constant(value) if value.bits() > 256 => {
                self.fmt(format_args!("<integer constant: {} bits>", value.bits()))
            }
            IntegerTerm::Constant(value) => self.fmt(format_args!("{value}")),
            // An Integer model field prints as the field it is; the mint
            // registered it, because the value lives inside the instance fact
            // and the term carries nothing to recover it from.
            IntegerTerm::Variable(variable) => {
                match crate::kernel::model_fields::model_field_spelling(*variable) {
                    Some(spelling) => self.push(&spelling),
                    None => self.fmt(format_args!("i{}", variable.0)),
                }
            }
            IntegerTerm::Machine(value) => {
                self.fmt(format_args!("machine-integer<{:?}>(", value.ty()));
                self.bitvector(value.value());
                self.push(")");
            }
            IntegerTerm::Negate(value) => {
                self.push("(-");
                self.integer_shared(value);
                self.push(")");
            }
            IntegerTerm::Add(left, right) => self.integer_binary(left, "+", right),
            IntegerTerm::Subtract(left, right) => self.integer_binary(left, "-", right),
            IntegerTerm::Multiply(left, right) => self.integer_binary(left, "*", right),
            IntegerTerm::PureFunctionApplication(application) => {
                self.push(application.name());
                self.push("(");
                self.pure_arguments(application.arguments());
                self.push(")");
            }
            IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
                self.push("match ");
                self.algebraic(scrutinee);
                self.push(" { ");
                for (index, arm) in arms.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&arm.variant);
                    self.push(" => ");
                    self.integer_shared(&arm.body);
                }
                self.push(" }");
            }
            IntegerTerm::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => {
                self.push("range-fold(index=");
                match index {
                    IntegerRangeFoldIndex::Int32 { start, end } => {
                        self.bitvector(start.value());
                        self.push("..");
                        self.bitvector(end.value());
                    }
                    IntegerRangeFoldIndex::Integer { start, end } => {
                        self.integer_shared(start);
                        self.push("..");
                        self.integer_shared(end);
                    }
                }
                self.fmt(format_args!(
                    ", acc=i{}, item=i{}, init=",
                    accumulator.0, item.0
                ));
                self.integer_shared(initial);
                self.push(", body=");
                self.integer_shared(body);
                self.push(")");
            }
        }
    }
    fn integer_shared(&mut self, value: &crate::kernel::SharedIntegerTerm) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        self.integer(value.as_ref());
        self.depth -= 1;
    }
    fn integer_binary(
        &mut self,
        left: &crate::kernel::SharedIntegerTerm,
        op: &str,
        right: &crate::kernel::SharedIntegerTerm,
    ) {
        self.push("(");
        self.integer_shared(left);
        self.push(op);
        self.integer_shared(right);
        self.push(")");
    }
    fn bitvector(&mut self, v: &Bitvector32Term) {
        if self.truncated || !self.visit() || self.depth >= MAX_DEPTH {
            self.truncated = true;
            return;
        }
        self.depth += 1;
        if let Bitvector32Term::MemoryLoad(snapshot, pointer) = v {
            // `memory` prints its own `snapshot=` prefix.
            self.push("load(");
            self.memory(snapshot.as_ref());
            self.push(", pointer=");
            self.pointer(pointer);
            self.push(")");
            self.depth -= 1;
            return;
        }
        // A registered load variable is a name for one load, and the load it
        // names is the part a reader compares. Printing the bare id made two
        // reads of one address at two snapshots look like two unrelated
        // numbers, and printing only the address made them look identical;
        // neither says which memory each side reads, which is the whole
        // question wherever a load fact fails to carry across a step.
        if let Bitvector32Term::Variable(variable) = v
            && crate::kernel::is_load_variable(variable)
            && let Some((snapshot, pointer)) = crate::kernel::registered_load_for_variable(variable)
        {
            self.fmt(format_args!("v{}=load(", variable.0));
            self.memory(snapshot.memory());
            self.push(", pointer=");
            self.pointer(&pointer);
            self.push(")");
            self.depth -= 1;
            return;
        }
        match v {
            Bitvector32Term::Constant(v) => self.fmt(format_args!("{v}")),
            Bitvector32Term::Int64Constant(v) => self.fmt(format_args!("{v}i64")),
            Bitvector32Term::UInt64Constant(v) => self.fmt(format_args!("{v}u64")),
            // A model-field variable is a name for one field of one instance,
            // and the field is the part a reader compares. The id is kept
            // beside it here, as a load variable's is, because this renderer
            // prints the kernel's own goal and premises.
            Bitvector32Term::Variable(v)
                if let Some(spelling) = crate::kernel::model_fields::model_field_spelling(*v) =>
            {
                self.fmt(format_args!("v{}={spelling}", v.0))
            }
            Bitvector32Term::Variable(v) => self.fmt(format_args!("v{}", v.0)),
            Bitvector32Term::Add(a, b) => self.binary_bv("+", a, b),
            Bitvector32Term::Subtract(a, b) => self.binary_bv("-", a, b),
            Bitvector32Term::Multiply(a, b) => self.binary_bv("*", a, b),
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                self.push("fold(");
                self.bitvector(start);
                self.push("..");
                self.bitvector(end);
                self.push(", init=");
                self.bitvector(initial);
                self.fmt(format_args!(
                    ", acc=v{}, item=v{}, body=",
                    accumulator.0, item.0
                ));
                self.bitvector(body);
                self.push(")");
            }
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                for (index, argument) in arguments.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.bitvector(argument);
                }
                self.push(")");
            }
            Bitvector32Term::ClickFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                self.pure_arguments(arguments);
                self.push(")");
            }
            Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
                self.push("match ");
                self.algebraic(scrutinee);
                self.push(" { ");
                for (index, arm) in arms.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&arm.variant);
                    self.push(" => ");
                    self.bitvector(&arm.body);
                }
                self.push(" }");
            }
            Bitvector32Term::PointerAddress(pointer) => {
                self.push("address(");
                self.pointer(pointer);
                self.push(")");
            }
            _ => self.push("bitvector(<bounded opaque operation>)"),
        }
        self.depth -= 1;
    }
    fn binary_bv(&mut self, op: &str, left: &Bitvector32Term, right: &Bitvector32Term) {
        self.push("(");
        self.bitvector(left);
        self.push(op);
        self.bitvector(right);
        self.push(")");
    }
    fn offset(&mut self, o: &PointerOffsetTerm, _depth: usize) {
        if self.depth >= MAX_DEPTH || self.truncated {
            self.truncated = true;
            return;
        }
        match o {
            PointerOffsetTerm::Constant(v) => self.fmt(format_args!("{v}")),
            PointerOffsetTerm::Variable(v) => self.fmt(format_args!("off{}", v.0)),
            PointerOffsetTerm::Add(a, b) => {
                self.depth += 1;
                self.push("(");
                self.offset(a, 0);
                self.push("+");
                self.offset(b, 0);
                self.push(")");
                self.depth -= 1;
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width }
            | PointerOffsetTerm::Int64Scaled {
                value, byte_width, ..
            } => {
                self.bitvector(value);
                self.fmt(format_args!("*{byte_width}"));
            }
        }
    }
    fn pointer(&mut self, p: &Pointer) {
        self.push("pointer(");
        match &p.block {
            crate::kernel::PointerBlock::Concrete(s) | crate::kernel::PointerBlock::Function(s) => {
                self.push(s)
            }
            crate::kernel::PointerBlock::Heap(id) => self.fmt(format_args!("heap#{id}")),
            crate::kernel::PointerBlock::Temporary(id) => self.fmt(format_args!("temporary#{id}")),
            crate::kernel::PointerBlock::Symbolic(v)
            | crate::kernel::PointerBlock::FunctionSymbolic(v)
            | crate::kernel::PointerBlock::ExternalObject(v) => {
                self.fmt(format_args!("symbolic#{}", v.0))
            }
            crate::kernel::PointerBlock::ExternalArgument => self.push("external"),
            crate::kernel::PointerBlock::StringLiteral { identity, .. } => self.push(identity),
        };
        self.push("+");
        self.offset(&p.offset, 0);
        self.push(")");
    }
    fn resource(&mut self, resource: &CResource) {
        match resource {
            CResource::Memory(range) => {
                self.push("memory-resource(");
                self.pointer(range.base());
                self.push("[");
                self.bitvector(range.start());
                self.push("..");
                self.bitvector(range.end());
                self.push("])");
            }
            CResource::Composite { name, arguments } => self.fmt(format_args!(
                "composite-resource({name}, {} args)",
                arguments.len()
            )),
            CResource::Token { name, arguments } => self.fmt(format_args!(
                "token-resource({name}, {} args)",
                arguments.len()
            )),
            CResource::Instance(instance) => {
                self.fmt(format_args!("resource-instance({})", instance.name()))
            }
        }
    }
    fn memory(&mut self, memory: &CMemory) {
        let label = self.labels.label(memory);
        self.fmt(format_args!("snapshot#{label}"));
    }
    fn state(&mut self, state: &CState) {
        self.push("state(");
        self.memory(state.memory());
        self.push(")");
    }
    fn cvalue(&mut self, value: &crate::kernel::CValue) {
        match value {
            crate::kernel::CValue::Void => self.push("void"),
            crate::kernel::CValue::Bool(v) => {
                self.push("bool(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int16(v) => {
                self.push("int16(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int32(v) => {
                self.push("int32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt8(v) => {
                self.push("uint8(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt16(v) => {
                self.push("uint16(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt32(v) => {
                self.push("uint32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int64(v) => {
                self.push("int64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt64(v) => {
                self.push("uint64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Float32(v) => {
                self.push("float32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Float64(v) => {
                self.push("float64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Pointer(p) => self.pointer(p),
        }
    }
    fn outcome(&mut self, outcome: &CExpressionOutcome) {
        match outcome {
            CExpressionOutcome::Value(value) => self.cvalue(value),
            CExpressionOutcome::UndefinedBehavior(_) => self.push("undefined-behavior"),
            CExpressionOutcome::RuntimeError(_) => self.push("runtime-error"),
        }
    }
    fn condition_outcome(&mut self, outcome: &crate::kernel::CConditionOutcome) {
        self.push(match outcome {
            crate::kernel::CConditionOutcome::Value(true) => "true",
            crate::kernel::CConditionOutcome::Value(false) => "false",
            crate::kernel::CConditionOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::CConditionOutcome::RuntimeError(_) => "runtime-error",
        });
    }
    fn statement_outcome(&mut self, outcome: &crate::kernel::CStatementOutcome) {
        self.push(match outcome {
            crate::kernel::CStatementOutcome::Normal(_) => "normal",
            crate::kernel::CStatementOutcome::Break(_) => "break",
            crate::kernel::CStatementOutcome::Continue(_) => "continue",
            crate::kernel::CStatementOutcome::Jump { .. } => "jump",
            crate::kernel::CStatementOutcome::Return { .. } => "return",
            crate::kernel::CStatementOutcome::Throw { .. } => "throw",
            crate::kernel::CStatementOutcome::VerificationDiverges => "verification-diverges",
            crate::kernel::CStatementOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::CStatementOutcome::RuntimeError(_) => "runtime-error",
        });
    }
    fn function_outcome(&mut self, outcome: &crate::kernel::CFunctionOutcome) {
        self.push(match outcome {
            crate::kernel::CFunctionOutcome::Return { .. } => "return",
            crate::kernel::CFunctionOutcome::Throw { .. } => "throw",
            crate::kernel::CFunctionOutcome::VerificationDiverges => "verification-diverges",
            crate::kernel::CFunctionOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::CFunctionOutcome::RuntimeError(_) => "runtime-error",
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::SharedIntegerTerm;

    #[test]
    fn renders_integer_fold_and_scope() {
        let integer = IntegerTerm::Add(
            SharedIntegerTerm::from(IntegerTerm::from(2)),
            SharedIntegerTerm::from(IntegerTerm::from(3)),
        );
        let proposition = Proposition::ForAll {
            var: crate::kernel::Variable(7),
            sort: crate::kernel::Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(integer),
                Term::Integer(IntegerTerm::from(5)),
            )),
        };
        let rendered = render_proposition(&proposition);
        assert!(rendered.contains("∀v7:Integer"));
        assert!(rendered.contains("2"));
    }

    #[test]
    fn deep_dag_is_bounded_and_marks_truncation() {
        let mut proposition = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        for _ in 0..128 {
            proposition = Proposition::Not(Box::new(proposition));
        }
        let rendered = render_proposition(&proposition);
        assert!(rendered.len() <= MAX_BYTES + "\n… <proof proposition truncated>".len());
        assert!(rendered.contains("truncated") || rendered.contains('…'));
    }

    #[test]
    fn integer_comparison_keeps_operands_and_operator() {
        let left = SharedIntegerTerm::from(IntegerTerm::from(11));
        let right = SharedIntegerTerm::from(IntegerTerm::from(19));
        let proposition =
            Proposition::ConditionIs(ConditionTerm::IntegerLessThan(left, right), true);
        let rendered = render_proposition(&proposition);
        assert!(rendered.contains("integer-condition"));
        assert!(rendered.contains("<"));
        assert!(rendered.contains("11"));
        assert!(rendered.contains("19"));
    }

    #[test]
    fn range_fold_keeps_bounds_and_body_variables() {
        let fold = Bitvector32Term::RangeFold {
            start: Box::new(Bitvector32Term::Constant(1)),
            end: Box::new(Bitvector32Term::Constant(4)),
            initial: Box::new(Bitvector32Term::Constant(0)),
            accumulator: crate::kernel::Variable(8),
            item: crate::kernel::Variable(9),
            body: Box::new(Bitvector32Term::Variable(crate::kernel::Variable(10))),
        };
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(fold),
            Term::Bitvector32(Bitvector32Term::Constant(0)),
        ));
        assert!(rendered.contains("fold("));
        assert!(rendered.contains("acc=v8"));
        assert!(rendered.contains("body=v10"));
    }

    fn loadable_at(memory: CMemory) -> Proposition {
        Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: crate::kernel::PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(1),
        }
    }

    /// A label says what a reader needs it to say: equal memory reads as one
    /// snapshot whether or not it shares storage roots, and memory that differs
    /// reads as another. The five `Arc` addresses this used to print made two
    /// separately built empty snapshots look like different memory.
    #[test]
    fn equal_snapshots_share_one_label_and_different_memory_does_not() {
        let first = CMemory::default();
        let shared = first.clone();
        let rebuilt = CMemory::default();
        let different = CMemory::new().with_block("block", 16);
        assert_ne!(first.diagnostic_identity(), rebuilt.diagnostic_identity());

        let first_text = render_proposition(&loadable_at(first));
        assert!(first_text.contains("snapshot#1"), "{first_text}");
        assert_eq!(first_text, render_proposition(&loadable_at(shared)));
        assert_eq!(first_text, render_proposition(&loadable_at(rebuilt)));

        // Within one report the labels are the order of first appearance, so
        // two different memories are visibly two.
        let mut labels = SnapshotLabels::default();
        let empty = render_proposition_labeled(&loadable_at(CMemory::default()), &mut labels);
        let blocked = render_proposition_labeled(&loadable_at(different), &mut labels);
        assert!(empty.contains("snapshot#1"), "{empty}");
        assert!(blocked.contains("snapshot#2"), "{blocked}");
    }

    /// The comparison stops at its cap rather than growing with the report.
    #[test]
    fn snapshot_labels_stop_comparing_past_their_cap() {
        let mut labels = SnapshotLabels::default();
        for size in 0..MAX_SNAPSHOT_LABELS as u32 {
            let memory = CMemory::new().with_block(format!("block{size}"), 16);
            assert_eq!(labels.label(&memory), size as usize + 1);
        }
        let overflowing = CMemory::new().with_block("block0", 16);
        assert_eq!(labels.label(&overflowing), 1, "an earlier label still wins");
        let beyond = CMemory::new().with_block("beyond", 16);
        assert_eq!(labels.label(&beyond), MAX_SNAPSHOT_LABELS + 1);
        assert_eq!(labels.label(&beyond), MAX_SNAPSHOT_LABELS + 1);
    }

    #[test]
    fn non_ascii_truncation_is_safe() {
        let proposition = Proposition::Predicate {
            name: "λ".repeat(MAX_BYTES),
            arguments: Vec::new(),
        };
        let rendered = render_proposition(&proposition);
        assert!(rendered.is_char_boundary(rendered.len()));
        assert!(rendered.contains("truncated"));
    }

    #[test]
    fn bounded_shared_integer_dag() {
        for depth in [8usize, 16, 32, 64] {
            let mut child =
                SharedIntegerTerm::from(IntegerTerm::Variable(crate::kernel::Variable(1)));
            for _ in 0..depth {
                child = SharedIntegerTerm::from(IntegerTerm::Add(child.clone(), child));
            }
            let rendered = render_proposition(&Proposition::Equal(
                Term::Integer(child.as_ref().clone()),
                Term::Integer(IntegerTerm::from(0)),
            ));
            assert!(rendered.len() <= MAX_BYTES + 64);
            if depth >= 32 {
                assert!(rendered.contains("truncated"));
            }
        }
    }

    #[test]
    fn deep_bitvector_tree_is_bounded() {
        let mut value = Bitvector32Term::Constant(1);
        for _ in 0..128 {
            value = Bitvector32Term::Add(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
        }
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(value),
            Term::Bitvector32(Bitvector32Term::Constant(0)),
        ));
        assert!(rendered.contains("truncated"));
    }

    #[test]
    fn integer_range_fold_renders_bounds_and_body() {
        let start = SharedIntegerTerm::from(IntegerTerm::from(2));
        let end = SharedIntegerTerm::from(IntegerTerm::from(9));
        let body = SharedIntegerTerm::from(IntegerTerm::Add(
            SharedIntegerTerm::from(IntegerTerm::Variable(crate::kernel::Variable(8))),
            SharedIntegerTerm::from(IntegerTerm::Variable(crate::kernel::Variable(9))),
        ));
        let fold = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer { start, end },
            initial: SharedIntegerTerm::from(IntegerTerm::from(0)),
            accumulator: crate::kernel::Variable(8),
            item: crate::kernel::Variable(9),
            body,
        };
        let rendered = render_proposition(&Proposition::Equal(
            Term::Integer(fold),
            Term::Integer(IntegerTerm::from(0)),
        ));
        assert!(rendered.contains("2"));
        assert!(rendered.contains("9"));
        assert!(rendered.contains("i8"));
        assert!(rendered.contains("i9"));
    }

    #[test]
    fn machine_and_c_value_types_remain_visible() {
        let int32 = render_proposition(&Proposition::Equal(
            Term::CValue(crate::kernel::CValue::Int32(Bitvector32Term::Constant(1))),
            Term::CValue(crate::kernel::CValue::UInt32(Bitvector32Term::Constant(1))),
        ));
        assert!(int32.contains("int32(1)"));
        assert!(int32.contains("uint32(1)"));
    }
}
