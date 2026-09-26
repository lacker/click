//! Checked read summaries for `Integer`-valued range-fold functions, and the
//! explicit application-framing rule they support
//! (`design/dfs-gaps/fold-read-range-inference.md`, delivery steps 1 and 2).
//!
//! An `Integer` function over an `int32[]` argument is an opaque application
//! whose array argument names a whole-block snapshot. A fact about
//! `unmarked(visited, 0, i)` therefore dies at `visited[i] = 1` even though
//! the fold reads only the cells below `i`. This module adds two independent
//! checks that together bridge that store, and nothing else:
//!
//! 1. **Definition checking** ([`CheckedFoldReadSummary::check`]). The body of
//!    one declared function, lowered once per verification in the kernel's
//!    specification vocabulary, is walked against an explicit whitelist. It is
//!    accepted only when it is a top-level `int32`-indexed range fold whose
//!    every memory read is exactly the one array parameter at the fold's own
//!    item binder. Anything else -- another index, a nested fold, a call, an
//!    address escape, a read in an endpoint or the initial accumulator --
//!    declines the *whole* definition. The resulting handle's fields are
//!    private, so the Surface can register a body but never state a summary.
//! 2. **Framing** ([`frame_fold_application_transport`]). Two applications of
//!    one summarized function whose arguments agree except for the array
//!    argument's snapshot are equal when every recorded step between the two
//!    snapshots is shown not to write a byte of the instantiated interval
//!    `base + 4*k` for `start <= k < end`. Each step is decided from its own
//!    recorded write set and the querying context's exact facts; nothing is
//!    recorded on the edge or cached, so the answer is a checked derivation of
//!    this query, never an assumption-free name.
//!
//! **Why this is sound.** The value of `f(array-ref(m, p), args)` is the fold
//! body evaluated with its reads at `m` (an `unfold` states it at a state whose
//! block epoch is `m`). Definition checking guarantees the body reads memory
//! only as the typed `int32` cell `p + 4*k` for the fold item `k`, and the fold
//! visits exactly `start <= k < end`, so the value is a function of the
//! arguments and of those cells' contents alone (finite fold induction: equal
//! initial values, and each iteration sees the same accumulator, index and
//! cell). Framing guarantees those cells hold the same bytes at both
//! snapshots. Pointer offsets are exact `i64` sums of sign-extended scaled
//! `int32` terms (`PointerOffsetTerm::Int32Scaled`), so the cells occupy the
//! contiguous bytes `[p + 4*start, p + 4*end)` with no wraparound, and a write
//! misses them exactly when it ends at or below the first byte or starts at or
//! above the last one. Emptiness is used only when a fact or the syntax proves
//! `end <= start`.
//!
//! **What it never does.** It inserts no viewability or initialization guard,
//! produces no resource fact, and grants no C access: the only thing it proves
//! is a logical equality between two opaque applications. It crosses no
//! allocation, free, lifetime end, loop havoc, forgotten-cell or claim edge
//! except where the kernel's assumption-free block rule already proves the
//! whole block untouched.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::primitives::*;
use super::resource_tracker::{Resource, step_effect};

/// One declared `Integer` function body, in the kernel's specification
/// vocabulary, with its parameters left as the names the body refers to.
///
/// This is program data, exactly as [`crate::kernel::CPureFunctionDefinition`]
/// is: registering it states nothing. The kernel decides whether it admits a
/// read summary.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct CFoldReadDefinition {
    name: String,
    parameters: Vec<(String, CType)>,
    body: SpecIntegerExpression,
}

impl CFoldReadDefinition {
    pub fn new(
        name: impl Into<String>,
        parameters: Vec<(String, CType)>,
        body: SpecIntegerExpression,
    ) -> Self {
        Self {
            name: name.into(),
            parameters,
            body,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    fn fingerprint(&self) -> u64 {
        use std::hash::{Hash, Hasher};
        crate::instrumentation::record_deterministic_work(1);
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        hasher.finish()
    }
}

/// Where one endpoint of the summarized fold comes from.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FoldEndpointTemplate {
    /// The `int32` scalar parameter at this position.
    Parameter(usize),
    /// A literal `int32` value.
    Literal(u32),
}

/// A kernel-checked read summary of one declared function.
///
/// Its only constructor is [`Self::check`], which validates the declared body.
/// Every field is private: a caller outside this module can hold and pass a
/// summary but cannot state one, so no interval reaches the framing rule
/// except the one the body's own fold writes.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CheckedFoldReadSummary {
    name: String,
    fingerprint: u64,
    parameter_types: Vec<CType>,
    array_parameter: usize,
    element_width: u32,
    start: FoldEndpointTemplate,
    end: FoldEndpointTemplate,
    accumulator: Variable,
    item: Variable,
}

/// Why a definition admits no read summary. Every reason declines the whole
/// definition; nothing is summarized partially.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FoldReadDecline {
    /// The body is not a top-level range fold over `int32` endpoints.
    NotATopLevelInt32Fold,
    /// The parameters are not exactly one `int32[]` array and `int32` scalars.
    UnsupportedParameters(String),
    /// An endpoint is neither an `int32` scalar parameter nor a literal.
    UnsupportedEndpoint,
    /// The initial accumulator reads memory, the accumulator, or the item, or
    /// uses a constructor outside the whitelist.
    UnsupportedInitialValue(String),
    /// The body reads the array somewhere other than at the fold's own item.
    ReadOutsideFoldIndex,
    /// The body uses a constructor outside the whitelist: a call (opaque
    /// helper or recursion), a nested fold, another memory, an address
    /// escape, a quantifier, a resource or a free variable.
    UnsupportedConstruct(String),
}

impl std::fmt::Display for FoldReadDecline {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotATopLevelInt32Fold => {
                formatter.write_str("its body is not a top-level `int32`-indexed range fold")
            }
            Self::UnsupportedParameters(detail) => write!(
                formatter,
                "its parameters are not one `int32[]` array plus `int32` scalars ({detail})"
            ),
            Self::UnsupportedEndpoint => formatter
                .write_str("a fold endpoint is not an `int32` scalar parameter or a literal"),
            Self::UnsupportedInitialValue(detail) => write!(
                formatter,
                "the fold's initial value is not a memory-independent term ({detail})"
            ),
            Self::ReadOutsideFoldIndex => formatter.write_str(
                "the fold body reads the array at an index other than the fold's own binder",
            ),
            Self::UnsupportedConstruct(detail) => write!(
                formatter,
                "the fold body uses a construct outside the checked subset ({detail})"
            ),
        }
    }
}

/// The instantiated support of one application: the typed `int32` cells
/// `base + element_width * k` for `start <= k < end`, read at `memory`.
#[derive(Clone, Debug)]
pub(crate) struct FoldReadInterval {
    pub(crate) memory: CMemory,
    pub(crate) base: Pointer,
    pub(crate) start: Bitvector32Term,
    pub(crate) end: Bitvector32Term,
    pub(crate) element_width: u32,
}

/// What the body walk may see at one position.
#[derive(Clone, Copy, Eq, PartialEq)]
enum Scope {
    /// The endpoints and the initial value: no accumulator, item, or read.
    Outside,
    /// The fold body: the accumulator, the item and the exact array read.
    Body,
}

struct BodyChecker<'a> {
    parameters: &'a [(String, CType)],
    array_name: &'a str,
    accumulator: Variable,
    item: Variable,
}

impl CheckedFoldReadSummary {
    /// Validates one declared body and returns its read summary, or the reason
    /// the definition declines. Work is one unit per visited specification
    /// node, so the check is linear in the selected body.
    pub fn check(definition: &CFoldReadDefinition) -> Result<Self, FoldReadDecline> {
        let parameters = &definition.parameters;
        let mut array_parameter = None;
        for (index, (name, c_type)) in parameters.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            match c_type {
                CType::Int32Pointer => {
                    if array_parameter.replace(index).is_some() {
                        return Err(FoldReadDecline::UnsupportedParameters(format!(
                            "a second array parameter `{name}`"
                        )));
                    }
                }
                CType::Int32 => {}
                other => {
                    return Err(FoldReadDecline::UnsupportedParameters(format!(
                        "`{name}` has type {other:?}"
                    )));
                }
            }
        }
        let Some(array_parameter) = array_parameter else {
            return Err(FoldReadDecline::UnsupportedParameters(
                "no `int32[]` parameter".into(),
            ));
        };
        let SpecIntegerExpression::RangeFold {
            index: SpecIntegerRangeFoldIndex::Int32 { start, end },
            initial,
            accumulator,
            item,
            body,
        } = &definition.body
        else {
            return Err(FoldReadDecline::NotATopLevelInt32Fold);
        };
        if accumulator == item {
            return Err(FoldReadDecline::UnsupportedConstruct(
                "the fold binders share one identity".into(),
            ));
        }
        let checker = BodyChecker {
            parameters,
            array_name: &parameters[array_parameter].0,
            accumulator: *accumulator,
            item: *item,
        };
        let start = checker.endpoint(start)?;
        let end = checker.endpoint(end)?;
        checker
            .integer(initial, Scope::Outside)
            .map_err(|decline| match decline {
                FoldReadDecline::UnsupportedConstruct(detail) => {
                    FoldReadDecline::UnsupportedInitialValue(detail)
                }
                FoldReadDecline::ReadOutsideFoldIndex => {
                    FoldReadDecline::UnsupportedInitialValue("it reads the array".into())
                }
                other => other,
            })?;
        checker.integer(body, Scope::Body)?;
        Ok(Self {
            name: definition.name.clone(),
            fingerprint: definition.fingerprint(),
            parameter_types: parameters.iter().map(|(_, c_type)| *c_type).collect(),
            array_parameter,
            element_width: 4,
            start,
            end,
            accumulator: *accumulator,
            item: *item,
        })
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    /// The support of one application of this function, or `None` when the
    /// application is not one this summary describes: another name, another
    /// arity, an argument of the wrong sort, or an array argument that is not
    /// an `int32` array reference.
    ///
    /// The endpoints are the application's own already-evaluated scalar
    /// arguments (or the literal the body writes); a historical endpoint keeps
    /// the load identity it was built with and is never reloaded.
    pub(crate) fn instantiate(
        &self,
        application: &SharedIntegerApplication,
    ) -> Option<FoldReadInterval> {
        crate::instrumentation::record_deterministic_work(1);
        let arguments = application.arguments();
        if application.name() != self.name || arguments.len() != self.parameter_types.len() {
            return None;
        }
        for (position, (argument, c_type)) in
            arguments.iter().zip(&self.parameter_types).enumerate()
        {
            crate::instrumentation::record_deterministic_work(1);
            let fits = match argument {
                PureFunctionArgument::ArrayRef {
                    pointer,
                    element_type,
                    ..
                } => {
                    position == self.array_parameter
                        && *element_type == CType::Int32
                        && matches!(pointer, CValue::Pointer(_))
                }
                PureFunctionArgument::Value(CValue::Int32(_)) => {
                    position != self.array_parameter && *c_type == CType::Int32
                }
                _ => false,
            };
            if !fits {
                return None;
            }
        }
        let PureFunctionArgument::ArrayRef {
            memory,
            pointer: CValue::Pointer(pointer),
            ..
        } = &arguments[self.array_parameter]
        else {
            return None;
        };
        let endpoint = |template: FoldEndpointTemplate| match template {
            FoldEndpointTemplate::Literal(value) => Some(Bitvector32Term::Constant(value)),
            FoldEndpointTemplate::Parameter(position) => match &arguments[position] {
                PureFunctionArgument::Value(CValue::Int32(value)) => Some(value.clone()),
                _ => None,
            },
        };
        Some(FoldReadInterval {
            memory: memory.clone(),
            base: pointer.pointer().clone(),
            start: endpoint(self.start)?,
            end: endpoint(self.end)?,
            element_width: self.element_width,
        })
    }
}

impl BodyChecker<'_> {
    fn scalar_parameter(&self, name: &str) -> Option<usize> {
        self.parameters
            .iter()
            .position(|(parameter, c_type)| parameter == name && *c_type == CType::Int32)
    }

    fn endpoint(&self, endpoint: &SpecExpression) -> Result<FoldEndpointTemplate, FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match endpoint {
            SpecExpression::CExpression(CExpression::Variable(name)) => self
                .scalar_parameter(name)
                .map(FoldEndpointTemplate::Parameter)
                .ok_or(FoldReadDecline::UnsupportedEndpoint),
            SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
                Ok(FoldEndpointTemplate::Literal(*value))
            }
            _ => Err(FoldReadDecline::UnsupportedEndpoint),
        }
    }

    fn unsupported(what: &str) -> FoldReadDecline {
        FoldReadDecline::UnsupportedConstruct(what.to_string())
    }

    /// A mathematical Integer term: literals, the accumulator inside the body,
    /// and total arithmetic over those. A machine-backed term is refused
    /// because its bitvector could hold a read this walk does not see.
    fn integer_term(&self, term: &IntegerTerm, scope: Scope) -> Result<(), FoldReadDecline> {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match term {
                IntegerTerm::Constant(_) => {}
                IntegerTerm::Variable(variable)
                    if scope == Scope::Body && *variable == self.accumulator => {}
                IntegerTerm::Variable(_) => {
                    return Err(Self::unsupported("a free Integer variable"));
                }
                IntegerTerm::Negate(inner) => pending.push(inner.as_ref()),
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right) => {
                    pending.push(left.as_ref());
                    pending.push(right.as_ref());
                }
                IntegerTerm::Machine(_) => {
                    return Err(Self::unsupported("an unevaluated machine value"));
                }
                IntegerTerm::PureFunctionApplication(_) => {
                    return Err(Self::unsupported("a function call"));
                }
                IntegerTerm::AlgebraicMatch { .. } => {
                    return Err(Self::unsupported("an algebraic match"));
                }
                IntegerTerm::RangeFold { .. } => return Err(Self::unsupported("a nested fold")),
            }
        }
        Ok(())
    }

    fn integer(
        &self,
        expression: &SpecIntegerExpression,
        scope: Scope,
    ) -> Result<(), FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            SpecIntegerExpression::Term(term) => self.integer_term(term, scope),
            SpecIntegerExpression::FromMachine(machine) => self.machine(machine, scope),
            SpecIntegerExpression::Negate(inner) => self.integer(inner, scope),
            SpecIntegerExpression::Add(left, right)
            | SpecIntegerExpression::Subtract(left, right)
            | SpecIntegerExpression::Multiply(left, right) => {
                self.integer(left, scope)?;
                self.integer(right, scope)
            }
            SpecIntegerExpression::RangeFold { .. } => Err(Self::unsupported("a nested fold")),
            SpecIntegerExpression::PureFunctionApplication { .. } => {
                Err(Self::unsupported("a function call"))
            }
            SpecIntegerExpression::ResourceField(_) => Err(Self::unsupported("a resource field")),
            SpecIntegerExpression::AlgebraicMatch { .. } => {
                Err(Self::unsupported("an algebraic match"))
            }
        }
    }

    fn bitvector(&self, term: &Bitvector32Term, scope: Scope) -> Result<(), FoldReadDecline> {
        match term {
            Bitvector32Term::Constant(_) => Ok(()),
            Bitvector32Term::Variable(variable)
                if scope == Scope::Body && *variable == self.item =>
            {
                Ok(())
            }
            _ => Err(Self::unsupported("an evaluated machine term")),
        }
    }

    /// Whether `pointer` is exactly the array parameter at the fold's item:
    /// `v + 4 * k`, matched by the item's identity rather than its spelling.
    fn is_exact_array_cell(&self, pointer: &SpecExpression) -> bool {
        let SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width: 4,
        } = pointer
        else {
            return false;
        };
        matches!(
            pointer.as_ref(),
            SpecExpression::CExpression(CExpression::Variable(name)) if name == self.array_name
        ) && matches!(
            elements.as_ref(),
            SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(variable)))
                if *variable == self.item
        )
    }

    fn machine(&self, expression: &SpecExpression, scope: Scope) -> Result<(), FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            SpecExpression::Value(CValue::Int32(term) | CValue::Bool(term)) => {
                self.bitvector(term, scope)
            }
            SpecExpression::Value(_) => Err(Self::unsupported("a non-int32 value")),
            SpecExpression::CExpression(CExpression::Variable(name)) => {
                if self.scalar_parameter(name).is_some() {
                    Ok(())
                } else if name == self.array_name {
                    Err(Self::unsupported("the array pointer used as a value"))
                } else {
                    Err(Self::unsupported("a name that is not an int32 parameter"))
                }
            }
            SpecExpression::CExpression(_) => Err(Self::unsupported("an unlowered C expression")),
            SpecExpression::MemoryLoad {
                memory,
                pointer,
                value_type,
            } => {
                if scope != Scope::Body {
                    return Err(FoldReadDecline::ReadOutsideFoldIndex);
                }
                if *memory != SpecMemory::Current {
                    return Err(Self::unsupported("a read at another program point"));
                }
                if *value_type != CType::Int32 || !self.is_exact_array_cell(pointer) {
                    return Err(FoldReadDecline::ReadOutsideFoldIndex);
                }
                Ok(())
            }
            SpecExpression::Add(left, right)
            | SpecExpression::Subtract(left, right)
            | SpecExpression::Multiply(left, right) => {
                self.machine(left, scope)?;
                self.machine(right, scope)
            }
            SpecExpression::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.proposition(condition, scope)?;
                self.machine(then_branch, scope)?;
                self.machine(else_branch, scope)
            }
            SpecExpression::PointerOffset { .. } => {
                Err(Self::unsupported("a pointer value outside a read"))
            }
            SpecExpression::PureFunctionApplication { .. } => {
                Err(Self::unsupported("a function call"))
            }
            SpecExpression::RangeFold { .. } => Err(Self::unsupported("a nested fold")),
            _ => Err(Self::unsupported(
                "a machine expression outside the whitelist",
            )),
        }
    }

    fn proposition(
        &self,
        proposition: &SpecProposition,
        scope: Scope,
    ) -> Result<(), FoldReadDecline> {
        crate::instrumentation::record_deterministic_work(1);
        match proposition {
            SpecProposition::Comparison { left, right, .. } => {
                self.machine(left, scope)?;
                self.machine(right, scope)
            }
            SpecProposition::IntegerComparison { left, right, .. } => {
                self.integer(left, scope)?;
                self.integer(right, scope)
            }
            SpecProposition::And(left, right)
            | SpecProposition::Or(left, right)
            | SpecProposition::Implies(left, right) => {
                self.proposition(left, scope)?;
                self.proposition(right, scope)
            }
            SpecProposition::Not(inner) => self.proposition(inner, scope),
            _ => Err(Self::unsupported("a proposition outside the whitelist")),
        }
    }
}

/// What the session registry holds for one declared name.
#[derive(Clone, Debug)]
enum RegisteredFoldRead {
    Checked(Arc<CheckedFoldReadSummary>),
    Declined(FoldReadDecline),
    /// Two different bodies were registered under one name in this session.
    /// Neither may govern framing, because unfolding might use the other.
    Conflicting,
}

thread_local! {
    /// The read summary of each registered `Integer` function, recorded once
    /// per verification session from the declared body, keyed by name and
    /// guarded by the body's fingerprint.
    static FOLD_READ_SUMMARIES: std::cell::RefCell<
        BTreeMap<String, (u64, RegisteredFoldRead)>,
    > = const { std::cell::RefCell::new(BTreeMap::new()) };
}

/// Records one declared body and its checked summary (or decline) for this
/// verification session. Registering a *different* body under a name already
/// registered poisons the name for the rest of the session: framing must
/// never follow a summary of a body other than the one unfolding states.
pub fn register_fold_read_definition(definition: CFoldReadDefinition) {
    let fingerprint = definition.fingerprint();
    let checked = match CheckedFoldReadSummary::check(&definition) {
        Ok(summary) => RegisteredFoldRead::Checked(Arc::new(summary)),
        Err(decline) => RegisteredFoldRead::Declined(decline),
    };
    FOLD_READ_SUMMARIES.with(|registry| {
        let mut registry = registry.borrow_mut();
        match registry.get_mut(&definition.name) {
            Some((recorded, _)) if *recorded == fingerprint => {}
            Some(entry) => entry.1 = RegisteredFoldRead::Conflicting,
            None => {
                registry.insert(definition.name.clone(), (fingerprint, checked));
            }
        }
    });
}

pub(crate) fn clear_fold_read_summaries() {
    FOLD_READ_SUMMARIES.with(|registry| registry.borrow_mut().clear());
}

/// Why no summary governs a name, for a refusal to print.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FoldReadUnavailable {
    NotRegistered,
    Declined(FoldReadDecline),
    Conflicting,
}

pub(crate) fn registered_fold_read_summary(
    name: &str,
) -> Result<Arc<CheckedFoldReadSummary>, FoldReadUnavailable> {
    crate::instrumentation::record_deterministic_work(1);
    FOLD_READ_SUMMARIES.with(|registry| match registry.borrow().get(name) {
        None => Err(FoldReadUnavailable::NotRegistered),
        Some((_, RegisteredFoldRead::Checked(summary))) => Ok(summary.clone()),
        Some((_, RegisteredFoldRead::Declined(decline))) => {
            Err(FoldReadUnavailable::Declined(decline.clone()))
        }
        Some((_, RegisteredFoldRead::Conflicting)) => Err(FoldReadUnavailable::Conflicting),
    })
}

// ---------------------------------------------------------------------------
// Framing
// ---------------------------------------------------------------------------

/// A checked explicit transport of one proposition across the steps between
/// the snapshots its fold applications name.
#[derive(Clone, Debug)]
pub(crate) struct CheckedFoldFrameTransport {
    /// How many application pairs were framed.
    pub(crate) framed_applications: usize,
    /// How many recorded steps the framing crossed in all.
    pub(crate) crossed_steps: usize,
}

/// Why a transport could not be framed, bounded for a refusal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum FoldFrameRefusal {
    /// The two propositions differ somewhere other than in the array
    /// snapshots of fold applications.
    ShapeMismatch,
    /// No two applications differ, so this rule has nothing to frame.
    NothingToFrame,
    /// The function has no checked read summary.
    NoSummary {
        name: String,
        reason: FoldReadUnavailable,
    },
    /// The two applications differ in a name, a scalar argument, the array
    /// pointer, or an argument sort.
    ApplicationsDiffer { name: String },
    /// Neither array snapshot is recorded as derived from the other.
    UnrelatedSnapshots { name: String },
    /// A step between the snapshots could not be shown to miss the interval.
    StepNotShownOutside {
        name: String,
        step: &'static str,
        detail: &'static str,
    },
}

impl std::fmt::Display for FoldFrameRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ShapeMismatch => formatter.write_str(
                "source and target differ outside the array snapshots of fold applications",
            ),
            Self::NothingToFrame => {
                formatter.write_str("no fold application differs between source and target")
            }
            Self::NoSummary { name, reason } => match reason {
                FoldReadUnavailable::NotRegistered => {
                    write!(formatter, "`{name}` has no checked read summary")
                }
                FoldReadUnavailable::Declined(decline) => {
                    write!(formatter, "`{name}` has no checked read summary: {decline}")
                }
                FoldReadUnavailable::Conflicting => write!(
                    formatter,
                    "`{name}` has no checked read summary: two different bodies were declared under that name"
                ),
            },
            Self::ApplicationsDiffer { name } => write!(
                formatter,
                "the two `{name}` applications differ in an endpoint, a scalar argument or the array pointer, not only in the array snapshot"
            ),
            Self::UnrelatedSnapshots { name } => write!(
                formatter,
                "the two `{name}` array snapshots are not on one recorded history"
            ),
            Self::StepNotShownOutside { name, step, detail } => write!(
                formatter,
                "a `{step}` step between the two `{name}` snapshots was not shown to miss the cells the fold reads: {detail}"
            ),
        }
    }
}

/// The explicit transport rule: `target` follows from `source` when the two
/// propositions are the same up to the array snapshots of summarized fold
/// applications, and every such pair is framed.
///
/// The walk is shallow and parallel: propositional connectives, the Integer
/// comparisons, and the Integer arithmetic spine. Anything else must be equal
/// on both sides. Work is linear in the two propositions plus, per framed
/// application pair, one unit per recorded step crossed.
pub(crate) fn frame_fold_application_transport(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
) -> Result<CheckedFoldFrameTransport, FoldFrameRefusal> {
    let mut checked = CheckedFoldFrameTransport {
        framed_applications: 0,
        crossed_steps: 0,
    };
    zip_proposition(source, target, assumptions, &mut checked)?;
    if checked.framed_applications == 0 {
        return Err(FoldFrameRefusal::NothingToFrame);
    }
    Ok(checked)
}

fn zip_proposition(
    source: &Proposition,
    target: &Proposition,
    assumptions: &PureFactContext,
    checked: &mut CheckedFoldFrameTransport,
) -> Result<(), FoldFrameRefusal> {
    crate::instrumentation::record_deterministic_work(1);
    match (source, target) {
        (
            Proposition::ConditionIs(left, left_value),
            Proposition::ConditionIs(right, right_value),
        ) if left_value == right_value => zip_condition(left, right, assumptions, checked),
        (Proposition::And(a, b), Proposition::And(c, d))
        | (Proposition::Or(a, b), Proposition::Or(c, d))
        | (Proposition::Implies(a, b), Proposition::Implies(c, d)) => {
            zip_proposition(a, c, assumptions, checked)?;
            zip_proposition(b, d, assumptions, checked)
        }
        (Proposition::Not(a), Proposition::Not(b)) => zip_proposition(a, b, assumptions, checked),
        (left, right) if left == right => Ok(()),
        _ => Err(FoldFrameRefusal::ShapeMismatch),
    }
}

fn zip_condition(
    source: &ConditionTerm,
    target: &ConditionTerm,
    assumptions: &PureFactContext,
    checked: &mut CheckedFoldFrameTransport,
) -> Result<(), FoldFrameRefusal> {
    use ConditionTerm as C;
    crate::instrumentation::record_deterministic_work(1);
    match (source, target) {
        (C::IntegerLessThan(a, b), C::IntegerLessThan(c, d))
        | (C::IntegerLessEqual(a, b), C::IntegerLessEqual(c, d))
        | (C::IntegerGreaterThan(a, b), C::IntegerGreaterThan(c, d))
        | (C::IntegerGreaterEqual(a, b), C::IntegerGreaterEqual(c, d))
        | (C::IntegerEqual(a, b), C::IntegerEqual(c, d))
        | (C::IntegerNotEqual(a, b), C::IntegerNotEqual(c, d)) => {
            zip_integer(a, c, assumptions, checked)?;
            zip_integer(b, d, assumptions, checked)
        }
        (left, right) if left == right => Ok(()),
        _ => Err(FoldFrameRefusal::ShapeMismatch),
    }
}

fn zip_integer(
    source: &SharedIntegerTerm,
    target: &SharedIntegerTerm,
    assumptions: &PureFactContext,
    checked: &mut CheckedFoldFrameTransport,
) -> Result<(), FoldFrameRefusal> {
    crate::instrumentation::record_deterministic_work(1);
    if source == target {
        return Ok(());
    }
    match (source.as_ref(), target.as_ref()) {
        (IntegerTerm::Negate(a), IntegerTerm::Negate(b)) => zip_integer(a, b, assumptions, checked),
        (IntegerTerm::Add(a, b), IntegerTerm::Add(c, d))
        | (IntegerTerm::Subtract(a, b), IntegerTerm::Subtract(c, d))
        | (IntegerTerm::Multiply(a, b), IntegerTerm::Multiply(c, d)) => {
            zip_integer(a, c, assumptions, checked)?;
            zip_integer(b, d, assumptions, checked)
        }
        (
            IntegerTerm::PureFunctionApplication(left),
            IntegerTerm::PureFunctionApplication(right),
        ) => {
            let crossed = frame_fold_applications(left, right, assumptions)?;
            checked.framed_applications += 1;
            checked.crossed_steps += crossed;
            Ok(())
        }
        _ => Err(FoldFrameRefusal::ShapeMismatch),
    }
}

/// Proves `left == right` for two applications of one summarized function
/// that differ only in the array argument's snapshot, returning how many
/// recorded steps were crossed.
pub(crate) fn frame_fold_applications(
    left: &SharedIntegerApplication,
    right: &SharedIntegerApplication,
    assumptions: &PureFactContext,
) -> Result<usize, FoldFrameRefusal> {
    let name = left.name().to_string();
    if left.name() != right.name() {
        return Err(FoldFrameRefusal::ApplicationsDiffer { name });
    }
    let summary = registered_fold_read_summary(left.name()).map_err(|reason| {
        FoldFrameRefusal::NoSummary {
            name: name.clone(),
            reason,
        }
    })?;
    let differ = || FoldFrameRefusal::ApplicationsDiffer { name: name.clone() };
    let left_interval = summary.instantiate(left).ok_or_else(differ)?;
    // Every argument but the array's snapshot must be the same term: the
    // same scalar values (so the same endpoints), the same pointer, the same
    // element type. Nothing here is proved equal; it is compared.
    for (position, (a, b)) in left.arguments().iter().zip(right.arguments()).enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let same = if position == summary.array_parameter {
            match (a, b) {
                (
                    PureFunctionArgument::ArrayRef {
                        pointer: left_pointer,
                        element_type: left_type,
                        ..
                    },
                    PureFunctionArgument::ArrayRef {
                        pointer: right_pointer,
                        element_type: right_type,
                        ..
                    },
                ) => left_pointer == right_pointer && left_type == right_type,
                _ => false,
            }
        } else {
            a == b
        };
        if !same {
            return Err(differ());
        }
    }
    if left.arguments().len() != right.arguments().len() {
        return Err(differ());
    }
    let PureFunctionArgument::ArrayRef {
        memory: right_memory,
        ..
    } = &right.arguments()[summary.array_parameter]
    else {
        return Err(differ());
    };
    let left_snapshot = intern_c_memory_ref(&left_interval.memory);
    let right_snapshot = intern_c_memory_ref(right_memory);
    if left_snapshot == right_snapshot {
        return Ok(0);
    }
    // Snapshots are content-addressed and each records its first derivation,
    // so the later snapshot's recorded history need not pass through the
    // earlier one: a second store to one cell re-derives from the state
    // before the first. Walk both back to a common snapshot, always stepping
    // the newer one, and check every step crossed on either side. Each step
    // relates two contents, so agreement on the interval along both walks is
    // agreement between the two ends. Arena ids strictly decrease along a
    // derivation, so the walk terminates, and it costs one unit per step.
    let empty = interval_proven_empty(&left_interval, assumptions);
    let (mut left_current, mut right_current) = (left_snapshot, right_snapshot);
    let mut crossed = 0;
    while left_current != right_current {
        crate::instrumentation::record_deterministic_work(1);
        let newer = if later_than(&left_current, &right_current) {
            &mut left_current
        } else if later_than(&right_current, &left_current) {
            &mut right_current
        } else {
            return Err(FoldFrameRefusal::UnrelatedSnapshots { name });
        };
        let Some(step) = newer.derivation() else {
            return Err(FoldFrameRefusal::UnrelatedSnapshots { name });
        };
        step_misses_interval(&step, newer, &left_interval, empty, assumptions).map_err(
            |(kind, detail)| FoldFrameRefusal::StepNotShownOutside {
                name: name.clone(),
                step: kind,
                detail,
            },
        )?;
        crossed += 1;
        *newer = step.base().clone();
    }
    Ok(crossed)
}

fn later_than(left: &SharedCMemory, right: &SharedCMemory) -> bool {
    let (left_arena, left_id) = left.arena_id();
    let (right_arena, right_id) = right.arena_id();
    left_arena == right_arena && left_id > right_id
}

/// Whether one recorded step leaves every cell of the interval unchanged.
fn step_misses_interval(
    step: &CMemoryDerivation,
    produced: &SharedCMemory,
    interval: &FoldReadInterval,
    empty: bool,
    assumptions: &PureFactContext,
) -> Result<(), (&'static str, &'static str)> {
    // A step the assumption-free whole-block rule separates from the array's
    // block leaves every byte of it alone, cells included. That rule reads no
    // fact, so this reuses its answer without widening it.
    let block_separate = matches!(
        step_effect::affects(
            step,
            produced,
            Resource::Block(&interval.base.block),
            &step_effect::Evidence {
                assumptions: &PureFactContext::new(),
                cross_loop_havoc: false,
            },
        ),
        step_effect::StepEffect::Separate(_)
    );
    if block_separate {
        return Ok(());
    }
    match step {
        CMemoryDerivation::Store { pointer, value, .. } => {
            if empty || access_misses_interval(pointer, value.byte_width(), interval, assumptions) {
                Ok(())
            } else {
                Err((
                    "store",
                    "no exact fact places the written bytes at or above the fold's end or below its start, and no stated separation holds them apart",
                ))
            }
        }
        // A seeded run is the stores it stands for, each framed as one.
        CMemoryDerivation::CellsSeeded { .. } => {
            let stores = step.seeded_stores().expect("a CellsSeeded edge");
            if empty
                || stores.iter().all(|(pointer, value)| {
                    access_misses_interval(pointer, value.byte_width(), interval, assumptions)
                })
            {
                Ok(())
            } else {
                Err((
                    "store",
                    "no exact fact places the written bytes at or above the fold's end or below its start, and no stated separation holds them apart",
                ))
            }
        }
        CMemoryDerivation::CallHavoc { mutable_ranges, .. } => {
            if empty
                || mutable_ranges
                    .iter()
                    .all(|written| range_misses_interval(written, interval, assumptions))
            {
                Ok(())
            } else {
                Err((
                    "call",
                    "a range the callee may write is not shown outside the fold's cells",
                ))
            }
        }
        other => Err((
            other.kind_name(),
            "only stores and calls with a checked write set are framed; allocation, free, lifetime, loop and forgetting steps keep the conservative whole-block rule",
        )),
    }
}

/// One exact linear form of a pointer offset: a constant plus integer
/// coefficients of opaque atoms. Every atom is a term whose value the offset
/// reads exactly (a sign-extended `int32`, a 64-bit index, or an offset
/// variable), so the form is the offset's `i64` value with no wraparound.
#[derive(Clone, Debug, Default)]
struct LinearOffset {
    constant: i128,
    atoms: BTreeMap<OffsetAtom, i128>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum OffsetAtom {
    Variable(Variable),
    Int32(Bitvector32Term),
    Int64 {
        value: Bitvector32Term,
        unsigned: bool,
    },
}

impl LinearOffset {
    fn of(offset: &PointerOffsetTerm) -> Self {
        let mut linear = Self::default();
        let mut pending = vec![(offset, 1i128)];
        while let Some((offset, sign)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                PointerOffsetTerm::Constant(value) => linear.constant += sign * i128::from(*value),
                PointerOffsetTerm::Variable(variable) => {
                    linear.add_atom(OffsetAtom::Variable(*variable), sign)
                }
                PointerOffsetTerm::Add(left, right) => {
                    pending.push((left, sign));
                    pending.push((right, sign));
                }
                PointerOffsetTerm::Int32Scaled { value, byte_width } => match value.as_const() {
                    Some(value) => {
                        linear.constant += sign * i128::from(value as i32) * i128::from(*byte_width)
                    }
                    None => linear.add_atom(
                        OffsetAtom::Int32(value.as_ref().clone()),
                        sign * i128::from(*byte_width),
                    ),
                },
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => linear.add_atom(
                    OffsetAtom::Int64 {
                        value: value.as_ref().clone(),
                        unsigned: *unsigned,
                    },
                    sign * i128::from(*byte_width),
                ),
            }
        }
        linear
    }

    fn add_atom(&mut self, atom: OffsetAtom, coefficient: i128) {
        let entry = self.atoms.entry(atom).or_insert(0);
        *entry += coefficient;
    }

    fn minus(mut self, other: &Self) -> Self {
        self.constant -= other.constant;
        for (atom, coefficient) in &other.atoms {
            crate::instrumentation::record_deterministic_work(1);
            self.add_atom(atom.clone(), -coefficient);
        }
        self.atoms.retain(|_, coefficient| *coefficient != 0);
        self
    }

    /// The form `element_width * sext(index) + constant`, when this is one:
    /// no atom at all (index `0`), or exactly one `int32` atom whose
    /// coefficient is the element width.
    fn as_scaled_index(&self, element_width: u32) -> Option<(Bitvector32Term, i128)> {
        match self.atoms.len() {
            // A constant delta names a constant index: the whole elements it
            // spans, when that is an `int32`, and the bytes left over.
            0 => {
                let width = i128::from(element_width);
                let index = self.constant.div_euclid(width);
                let index = i32::try_from(index).ok()?;
                Some((
                    Bitvector32Term::Constant(index as u32),
                    self.constant - i128::from(index) * width,
                ))
            }
            1 => {
                let (atom, coefficient) = self.atoms.iter().next()?;
                match atom {
                    OffsetAtom::Int32(index) if *coefficient == i128::from(element_width) => {
                        Some((index.clone(), self.constant))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// `element_width * sext(index) + constant` for `pointer` relative to `base`,
/// when both are in one block and the delta has that exact form.
fn scaled_index_from(
    pointer: &Pointer,
    base: &Pointer,
    element_width: u32,
) -> Option<(Bitvector32Term, i128)> {
    if pointer.block != base.block {
        return None;
    }
    LinearOffset::of(&pointer.offset)
        .minus(&LinearOffset::of(&base.offset))
        .as_scaled_index(element_width)
}

/// `left <= right` as signed `int32`, from syntax, constants, or one exact
/// fact. Only indexed lookups: nothing scans the context.
fn proven_signed_le(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if left == right {
        return true;
    }
    if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
        return (left as i32) <= (right as i32);
    }
    assumptions.exact_condition_value(&ConditionTerm::Bitvector32SignedLessEqual(
        Box::new(left.clone()),
        Box::new(right.clone()),
    )) == Some(true)
        || assumptions.exact_condition_value(&ConditionTerm::Bitvector32SignedLessThan(
            Box::new(left.clone()),
            Box::new(right.clone()),
        )) == Some(true)
}

/// `left < right` as signed `int32`, from constants or one exact fact.
fn proven_signed_lt(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
        return (left as i32) < (right as i32);
    }
    left != right
        && (assumptions.exact_condition_value(&ConditionTerm::Bitvector32SignedLessThan(
            Box::new(left.clone()),
            Box::new(right.clone()),
        )) == Some(true)
            || assumptions.exact_condition_value(&ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(right.clone()),
                Box::new(left.clone()),
            )) == Some(false))
}

/// The interval reads no cell because its end is proven at or below its
/// start. Unknown order is not emptiness.
fn interval_proven_empty(interval: &FoldReadInterval, assumptions: &PureFactContext) -> bool {
    proven_signed_le(&interval.end, &interval.start, assumptions)
}

/// Whether the `bytes` bytes at `pointer` miss every cell of the interval.
fn access_misses_interval(
    pointer: &Pointer,
    bytes: u32,
    interval: &FoldReadInterval,
    assumptions: &PureFactContext,
) -> bool {
    if bytes == 0 || pointer.blocks_proven_distinct(&interval.base) {
        return true;
    }
    if let Some((index, constant)) =
        scaled_index_from(pointer, &interval.base, interval.element_width)
    {
        let width = i128::from(interval.element_width);
        // The write starts at `width*index + constant`. At or above the end
        // cell's first byte when `index >= end` and `constant >= 0`; ending at
        // or below the start cell's first byte when `index < start` and the
        // write fits in the cell it starts in (`constant + bytes <= width`).
        let above = constant >= 0 && proven_signed_le(&interval.end, &index, assumptions);
        let below = constant + i128::from(bytes) <= width
            && proven_signed_lt(&index, &interval.start, assumptions);
        if above || below {
            return true;
        }
    }
    separated_by_stated_fact(
        |range| range_contains_interval(range, interval, assumptions),
        |range| range_contains_access(range, pointer, bytes, assumptions),
        &interval.base.block,
        &pointer.block,
        assumptions,
    )
}

/// Whether one range a callee may write misses every cell of the interval.
fn range_misses_interval(
    written: &CMemoryRange,
    interval: &FoldReadInterval,
    assumptions: &PureFactContext,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if written.base().blocks_proven_distinct(&interval.base) {
        return true;
    }
    if written.element_width() == interval.element_width
        && let Some((Bitvector32Term::Constant(0), 0)) =
            scaled_index_from(written.base(), &interval.base, interval.element_width)
    {
        // Same base and element width: the written cells are
        // `[written.start, written.end)` of the same array. The range must be
        // proven well formed first; a reversed range is never read as empty,
        // because nothing here decides what bytes such a write set covers.
        if proven_signed_le(written.start(), written.end(), assumptions)
            && (proven_signed_le(written.end(), &interval.start, assumptions)
                || proven_signed_le(&interval.end, written.start(), assumptions))
        {
            return true;
        }
    }
    separated_by_stated_fact(
        |range| range_contains_interval(range, interval, assumptions),
        |range| range_contains_range(range, written, assumptions),
        &interval.base.block,
        &written.base().block,
        assumptions,
    )
}

/// A stated `separate(memory(L), memory(R))` with the interval inside one side
/// and the write inside the other, both decided by exact order facts.
fn separated_by_stated_fact(
    holds_interval: impl Fn(&CMemoryRange) -> bool,
    holds_write: impl Fn(&CMemoryRange) -> bool,
    interval_block: &PointerBlock,
    write_block: &PointerBlock,
    assumptions: &PureFactContext,
) -> bool {
    assumptions
        .memory_separation_candidates(interval_block, write_block)
        .any(|(proposition, left, right)| {
            crate::instrumentation::record_deterministic_work(1);
            let oriented = holds_interval(left) && holds_write(right)
                || holds_interval(right) && holds_write(left);
            let holds =
                oriented && !assumptions.memory_ranges_overlap_after_base_equality(left, right);
            if holds {
                crate::kernel::record_implicit_reasoning_provenance(assumptions, proposition);
            }
            holds
        })
}

/// The interval's cells lie inside `range`: the same base and element width,
/// `range.start <= start` and `end <= range.end`.
fn range_contains_interval(
    range: &CMemoryRange,
    interval: &FoldReadInterval,
    assumptions: &PureFactContext,
) -> bool {
    range.element_width() == interval.element_width
        && matches!(
            scaled_index_from(&interval.base, range.base(), interval.element_width),
            Some((Bitvector32Term::Constant(0), 0))
        )
        && proven_signed_le(range.start(), &interval.start, assumptions)
        && proven_signed_le(&interval.end, range.end(), assumptions)
}

/// The `bytes` bytes at `pointer` lie inside one cell of `range`.
fn range_contains_access(
    range: &CMemoryRange,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    let width = range.element_width();
    let Some((index, constant)) = scaled_index_from(pointer, range.base(), width) else {
        return false;
    };
    constant >= 0
        && constant + i128::from(bytes) <= i128::from(width)
        && proven_signed_le(range.start(), &index, assumptions)
        && proven_signed_lt(&index, range.end(), assumptions)
}

/// `inner` lies inside `outer`: the same base and element width and nested
/// endpoints.
fn range_contains_range(
    outer: &CMemoryRange,
    inner: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    outer.element_width() == inner.element_width()
        && matches!(
            scaled_index_from(inner.base(), outer.base(), inner.element_width()),
            Some((Bitvector32Term::Constant(0), 0))
        )
        && proven_signed_le(inner.start(), inner.end(), assumptions)
        && proven_signed_le(outer.start(), inner.start(), assumptions)
        && proven_signed_le(inner.end(), outer.end(), assumptions)
}

#[cfg(test)]
mod tests;
