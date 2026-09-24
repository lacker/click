//! Read-only Click rendering for checked trace facts whose kernel shape is
//! more explicit than the current exact-premise citation machinery accepts.
//! This is presentation, never proof authority.

use super::*;
use crate::kernel::{IntegerTerm, PureFunctionArgument, SharedIntegerTerm};

const MAX_TRACE_FACT_DEPTH: usize = 24;
const MAX_TRACE_SNAPSHOTS: usize = 32;

struct TraceSurfaceView<'a> {
    parameters: &'a [syntax::C0Parameter],
    arguments: &'a [CExpression],
    current: &'a CState,
    locals: &'a BTreeMap<String, ContractExpression>,
    recent: Vec<(&'a SnapshotSelector, &'a CState)>,
}

impl Proof<'_> {
    pub(super) fn trace_surface_fact(&self, fact: &Proposition) -> Option<(String, bool)> {
        let view = self.execution_fixed_state_view()?;
        let locals = self.proof_local_values();
        let renderer = TraceSurfaceView {
            parameters: view.parameters,
            arguments: view.arguments,
            current: view.state,
            locals: &locals,
            recent: view.recorded_snapshots.recent(MAX_TRACE_SNAPSHOTS),
        };
        let surface = renderer.proposition(fact, &BTreeMap::new(), MAX_TRACE_FACT_DEPTH)?;
        let text = crate::surface::printing::source_click_proposition(&surface);
        if text.contains("__click_") {
            return None;
        }
        // The renderer is diagnostic-only. Promote its output to an exact
        // citation only when the normal lowering path confirms identity.
        let exact = self
            .lower_surface_proposition_direct(&surface, "trace fact")
            .is_ok_and(|lowered| lowered == *fact);
        Some((text, exact))
    }
}

impl TraceSurfaceView<'_> {
    fn proposition(
        &self,
        fact: &Proposition,
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ClickProposition> {
        let depth = depth.checked_sub(1)?;
        match fact {
            Proposition::Implies(left, right) => Some(ClickProposition::Implies(
                Box::new(self.proposition(left, binders, depth)?),
                Box::new(self.proposition(right, binders, depth)?),
            )),
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } => {
                let Sort::Algebraic(algebraic) = sort else {
                    return None;
                };
                if !algebraic.arguments.is_empty() {
                    return None;
                }
                let mut scoped = binders.clone();
                scoped.insert(*var, name.clone());
                Some(ClickProposition::Exists {
                    click_type: ClickType::Algebraic(AlgebraicTypeApplication::concrete(
                        algebraic.name.clone(),
                    )),
                    name: name.clone(),
                    written_name: Some(name.clone()),
                    body: Box::new(self.proposition(body, &scoped, depth)?),
                })
            }
            Proposition::ConditionIs(condition, polarity) => {
                let (left, operator, right) = match condition {
                    ConditionTerm::IntegerEqual(left, right) => (
                        self.integer(left, binders, depth)?,
                        if *polarity {
                            ComparisonOperator::Equal
                        } else {
                            ComparisonOperator::NotEqual
                        },
                        self.integer(right, binders, depth)?,
                    ),
                    ConditionTerm::IntegerLessEqual(left, right) => (
                        self.integer(left, binders, depth)?,
                        ComparisonOperator::LessEqual,
                        self.integer(right, binders, depth)?,
                    ),
                    ConditionTerm::Bitvector32Equal(left, right) => (
                        self.machine(left, binders, depth)?,
                        if *polarity {
                            ComparisonOperator::Equal
                        } else {
                            ComparisonOperator::NotEqual
                        },
                        self.machine(right, binders, depth)?,
                    ),
                    _ => return None,
                };
                if !*polarity && matches!(condition, ConditionTerm::IntegerLessEqual(..)) {
                    return None;
                }
                Some(ClickProposition::Comparison {
                    left,
                    operator,
                    right,
                })
            }
            _ => None,
        }
    }

    fn integer(
        &self,
        term: &SharedIntegerTerm,
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ContractExpression> {
        let depth = depth.checked_sub(1)?;
        match term.as_ref() {
            IntegerTerm::Constant(value) => {
                Some(ContractExpression::IntegerLiteral(value.to_string()))
            }
            IntegerTerm::Machine(value) => Some(ContractExpression::Call {
                name: "to_integer".into(),
                arguments: vec![self.machine(value.value(), binders, depth)?],
            }),
            IntegerTerm::Subtract(left, right) => Some(ContractExpression::Subtract(
                Box::new(self.integer(left, binders, depth)?),
                Box::new(self.integer(right, binders, depth)?),
            )),
            IntegerTerm::Add(left, right) => Some(ContractExpression::Add(
                Box::new(self.integer(left, binders, depth)?),
                Box::new(self.integer(right, binders, depth)?),
            )),
            IntegerTerm::PureFunctionApplication(application) => {
                self.call(application.name(), application.arguments(), binders, depth)
            }
            _ => None,
        }
    }

    fn machine(
        &self,
        term: &Bitvector32Term,
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ContractExpression> {
        let depth = depth.checked_sub(1)?;
        if let Bitvector32Term::ClickFunctionApplication { name, arguments } = term {
            return self.call(name, arguments, binders, depth);
        }
        if let Bitvector32Term::Variable(variable) = term {
            if let Some(name) = binders.get(variable) {
                return Some(ContractExpression::Binding(name.clone()));
            }
            if let Some((name, _)) = self.locals.iter().find(|(_, value)| {
                matches!(value, ContractExpression::CFragment(CExpression::Value(CValue::Int32(bits))) if bits == term)
            }) {
                return Some(ContractExpression::Binding(name.clone()));
            }
            if let Some((memory, pointer)) = crate::kernel::registered_load_for_variable(variable) {
                for (selector, state) in self.preferred_snapshots() {
                    let snapshot = crate::kernel::intern_c_memory_ref(state.memory());
                    if crate::kernel::canonical_form_of_load(snapshot.clone(), pointer.clone())
                        != *term
                    {
                        continue;
                    }
                    let load = Bitvector32Term::MemoryLoad(snapshot, Box::new(pointer.clone()));
                    if let Some(expression) =
                        super::super::surface_synthesis::synthesize_surface_machine_expression(
                            &load,
                            self.parameters,
                            self.arguments,
                            state,
                        )
                    {
                        return Some(ContractExpression::At {
                            selector: (*selector).clone(),
                            expression: Box::new(expression),
                        });
                    }
                }
                let load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer));
                return super::super::surface_synthesis::synthesize_surface_machine_expression(
                    &load,
                    self.parameters,
                    self.arguments,
                    self.current,
                );
            }
        }
        super::super::surface_synthesis::synthesize_surface_machine_expression(
            term,
            self.parameters,
            self.arguments,
            self.current,
        )
    }

    fn call(
        &self,
        name: &str,
        arguments: &[PureFunctionArgument],
        binders: &BTreeMap<crate::kernel::Variable, String>,
        depth: usize,
    ) -> Option<ContractExpression> {
        let depth = depth.checked_sub(1)?;
        let arguments = arguments
            .iter()
            .map(|argument| match argument {
                PureFunctionArgument::Value(CValue::Int32(value)) => {
                    self.machine(value, binders, depth)
                }
                PureFunctionArgument::ArrayRef {
                    memory,
                    pointer: CValue::Pointer(pointer),
                    ..
                } => self.array(memory, pointer.pointer()),
                PureFunctionArgument::Algebraic(term) => match &term.node {
                    crate::kernel::AlgebraicTermNode::Variable(variable) => binders
                        .get(variable)
                        .cloned()
                        .map(ContractExpression::Binding),
                    _ => None,
                },
                _ => None,
            })
            .collect::<Option<Vec<_>>>()?;
        Some(ContractExpression::Call {
            name: name.into(),
            arguments,
        })
    }

    fn array(&self, memory: &CMemory, pointer: &Pointer) -> Option<ContractExpression> {
        let base =
            self.parameters
                .iter()
                .zip(self.arguments)
                .find_map(|(parameter, argument)| {
                    let CExpression::Value(CValue::Pointer(value)) = argument else {
                        return None;
                    };
                    (value.pointer() == pointer).then(|| {
                        ContractExpression::CFragment(CExpression::Variable(
                            parameter.name().into(),
                        ))
                    })
                })?;
        if self.current.memory() == memory {
            return Some(base);
        }
        for (selector, state) in self.preferred_snapshots() {
            if state.memory() == memory {
                return Some(ContractExpression::At {
                    selector: (*selector).clone(),
                    expression: Box::new(base),
                });
            }
        }
        None
    }

    /// Named marks are the stable, author-chosen spelling when several
    /// recorded program points identify the same memory.
    fn preferred_snapshots(&self) -> impl Iterator<Item = &(&SnapshotSelector, &CState)> {
        self.recent
            .iter()
            .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
            .chain(
                self.recent
                    .iter()
                    .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
            )
    }
}
