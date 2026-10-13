//! Incremental paths of recorded strict signed orders. The weighted union
//! forest keeps ranks stable when paths join; no variable identifier order
//! is interpreted as a numeric fact.
use super::*;
use crate::persistent::PersistentMap;
use std::sync::{Arc, OnceLock};

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct VariableChains {
    sources: PersistentMap<(Variable, Variable), usize>,
    graph: Arc<OnceLock<ChainGraph>>,
}

#[derive(Clone, Debug, Default)]
struct ChainGraph {
    nodes: PersistentMap<Variable, ChainNode>,
}

#[derive(Clone, Debug)]
struct ChainNode {
    parent: Variable,
    delta: i64,
    first: i64,
    members: imbl::Vector<Variable>,
}

pub(in crate::kernel) struct ChainSpan<'a> {
    pub root: Variable,
    pub rank: usize,
    pub members: &'a imbl::Vector<Variable>,
}

impl ChainGraph {
    fn root(&self, mut variable: Variable) -> Option<(Variable, i64)> {
        let mut position = 0i64;
        loop {
            crate::instrumentation::record_deterministic_work(1);
            let node = self.nodes.get(&variable)?;
            if node.parent == variable {
                return Some((variable, position));
            }
            position = position.checked_add(node.delta)?;
            variable = node.parent;
        }
    }

    fn span(&self, variable: Variable) -> Option<ChainSpan<'_>> {
        let (root, coordinate) = self.root(variable)?;
        let node = self.nodes.get(&root)?;
        Some(ChainSpan {
            root,
            rank: usize::try_from(coordinate.checked_sub(node.first)?).ok()?,
            members: &node.members,
        })
    }

    fn singleton(&mut self, variable: Variable) {
        if !self.nodes.contains_key(&variable) {
            self.nodes.insert(
                variable,
                ChainNode {
                    parent: variable,
                    delta: 0,
                    first: 0,
                    members: imbl::vector![variable],
                },
            );
        }
    }

    fn connect(&mut self, left: Variable, right: Variable) {
        if left == right {
            return;
        }
        self.singleton(left);
        self.singleton(right);
        let (Some((left_root, _)), Some((right_root, _))) = (self.root(left), self.root(right))
        else {
            return;
        };
        if left_root == right_root {
            return;
        }
        let mut left_node = self.nodes.get(&left_root).unwrap().clone();
        let mut right_node = self.nodes.get(&right_root).unwrap().clone();
        if left_node.members.back() != Some(&left) || right_node.members.front() != Some(&right) {
            // A branching edge does not put every vertex of its two paths in
            // order. Leave these paths separate and use ordinary reasoning.
            return;
        }
        let Ok(left_length) = i64::try_from(left_node.members.len()) else {
            return;
        };
        let mut members = left_node.members.clone();
        members.append(right_node.members.clone());
        if left_node.members.len() >= right_node.members.len() {
            let Some(delta) = left_node
                .first
                .checked_add(left_length)
                .and_then(|end| end.checked_sub(right_node.first))
            else {
                return;
            };
            right_node.parent = left_root;
            right_node.delta = delta;
            right_node.members.clear();
            left_node.members = members;
        } else {
            let Some(first) = right_node.first.checked_sub(left_length) else {
                return;
            };
            let Some(delta) = first.checked_sub(left_node.first) else {
                return;
            };
            left_node.parent = right_root;
            left_node.delta = delta;
            left_node.members.clear();
            right_node.first = first;
            right_node.members = members;
        }
        self.nodes.insert(left_root, left_node);
        self.nodes.insert(right_root, right_node);
    }
}

impl VariableChains {
    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool, insert: bool) {
        let Some((Bitvector32Term::Variable(left), Bitvector32Term::Variable(right), true)) =
            condition_as_order_fact(condition, value)
        else {
            return;
        };
        if crate::kernel::is_load_variable(&left) || crate::kernel::is_load_variable(&right) {
            return;
        }
        let edge = (left, right);
        let count = self.sources.get(&edge).copied().unwrap_or(0);
        if insert {
            let graph = self
                .graph
                .get()
                .cloned()
                .or_else(|| self.sources.is_empty().then(ChainGraph::default));
            self.sources.insert(edge, count + 1);
            if count == 0 {
                let updated = OnceLock::new();
                if let Some(mut graph) = graph {
                    graph.connect(left, right);
                    let _ = updated.set(graph);
                }
                self.graph = Arc::new(updated);
            }
        } else if count > 1 {
            self.sources.insert(edge, count - 1);
        } else if count == 1 {
            self.sources.remove(&edge);
            // Removal can split a path. Rebuild only if a later query needs
            // it, rather than rebuilding at every withdrawal in a batch.
            self.graph = Arc::new(OnceLock::new());
        }
    }

    pub(in crate::kernel) fn span(&self, variable: Variable) -> Option<ChainSpan<'_>> {
        if self.sources.is_empty() {
            return None;
        }
        self.graph
            .get_or_init(|| {
                let mut graph = ChainGraph::default();
                for ((left, right), _) in self.sources.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    graph.connect(*left, *right);
                }
                graph
            })
            .span(variable)
    }

    pub(in crate::kernel) fn shares_sources(&self, other: &Self) -> bool {
        self.sources.shares_root_with(&other.sources)
            || match (self.graph.get(), other.graph.get()) {
                (Some(left), Some(right)) => left.nodes.shares_root_with(&right.nodes),
                _ => false,
            }
    }
}

impl PureFactContext {
    pub(super) fn decide_from_variable_chain(&self, condition: &ConditionTerm) -> Option<bool> {
        if implicit_reasoning_provenance_capturing() {
            return None;
        }
        let (lower, upper, strict) = condition_as_order_fact(condition, true)?;
        let node = |term: &Bitvector32Term| match term {
            Bitvector32Term::Variable(variable) => self.signed_variable_chains.span(*variable),
            _ => None,
        };
        let lower_span = node(&lower);
        let upper_span = node(&upper);
        if let (Some(left), Some(right)) = (&lower_span, &upper_span)
            && left.root == right.root
            && (left.rank < right.rank || (!strict && left.rank == right.rank))
        {
            return Some(true);
        }
        let direct = |left: Bitvector32Term, right: Bitvector32Term| {
            self.signed_order_bounds.get(&left).is_some_and(|bounds| {
                bounds.iter().any(|((lower, upper, _, outgoing), _)| {
                    *outgoing && lower == &left && upper == &right
                })
            })
        };
        if let Some(span) = upper_span {
            let first = Bitvector32Term::Variable(*span.members.front()?);
            if first != upper && direct(lower.clone(), first) {
                return Some(true);
            }
        }
        if let Some(span) = lower_span {
            let last = Bitvector32Term::Variable(*span.members.back()?);
            if last != lower && direct(last, upper) {
                return Some(true);
            }
        }
        None
    }
}

/// An exact symbolic array index. The base is returned separately so only
/// cells spelling that same base participate in the indexed path.
pub(in crate::kernel) fn array_index(
    offset: &PointerOffsetTerm,
) -> Option<(&PointerOffsetTerm, Variable, i64)> {
    static ZERO: PointerOffsetTerm = PointerOffsetTerm::Constant(0);
    let (base, index) = match offset {
        PointerOffsetTerm::Add(base, index) => (base.as_ref(), index.as_ref()),
        index => (&ZERO, index),
    };
    let PointerOffsetTerm::Int32Scaled { value, byte_width } = index else {
        return None;
    };
    let Bitvector32Term::Variable(variable) = value.as_ref() else {
        return None;
    };
    (*byte_width > 0 && !crate::kernel::is_load_variable(variable)).then_some((
        base,
        *variable,
        *byte_width,
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_paths_follow_values_not_variable_identifiers_or_insertion_order() {
        let variables = [
            Variable(901),
            Variable(103),
            Variable(507),
            Variable(211),
            Variable(809),
        ];
        for reverse in [false, true] {
            let mut context = PureFactContext::new();
            let mut edges = variables.windows(2).collect::<Vec<_>>();
            if reverse {
                edges.reverse();
            }
            for pair in edges {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(pair[0]),
                        Bitvector32Term::Variable(pair[1]),
                    ),
                    true,
                );
            }
            let first = context.signed_variable_chains.span(variables[0]).unwrap();
            assert_eq!(first.members.iter().copied().collect::<Vec<_>>(), variables);
            for (position, variable) in variables.iter().enumerate() {
                let span = context.signed_variable_chains.span(*variable).unwrap();
                assert_eq!(span.root, first.root);
                assert_eq!(span.rank, position);
            }
            let query = ConditionTerm::signed_less_than(
                Bitvector32Term::Variable(variables[0]),
                Bitvector32Term::Variable(variables[4]),
            );
            assert_eq!(context.decide_from_variable_chain(&query), Some(true));
            context.forget_condition_fact(
                &ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(variables[1]),
                    Bitvector32Term::Variable(variables[2]),
                ),
                true,
            );
            assert_eq!(context.decide_from_variable_chain(&query), None);
        }
    }

    #[test]
    fn branching_orders_do_not_order_siblings() {
        let variable = |id| Bitvector32Term::Variable(Variable(id));
        let context = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_than(variable(1), variable(3)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(variable(2), variable(3)),
                true,
            );
        assert_eq!(
            context.decide_from_variable_chain(&ConditionTerm::signed_less_than(
                variable(1),
                variable(2)
            )),
            None
        );
        assert_eq!(
            context.decide_from_variable_chain(&ConditionTerm::signed_less_than(
                variable(2),
                variable(1)
            )),
            None
        );
    }
}

#[cfg(test)]
mod memory_tests {
    use super::*;

    #[test]
    fn ordered_store_filter_matches_scalar_reference_and_checks_wide_neighbors() {
        let variables = [
            Variable(931),
            Variable(117),
            Variable(813),
            Variable(219),
            Variable(719),
            Variable(321),
            Variable(619),
            Variable(423),
            Variable(519),
        ];
        let mut context = PureFactContext::new();
        for pair in variables.windows(2) {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Variable(pair[0]),
                    Bitvector32Term::Variable(pair[1]),
                ),
                true,
            );
        }
        for (index, variable) in variables.iter().enumerate() {
            context = context.assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(*variable),
                    Bitvector32Term::Constant(index as u32 + 1),
                ),
                true,
            );
        }
        let pointer = |variable, stride| Pointer {
            block: PointerBlock::from("ordered"),
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(variable), stride),
        };
        let mut memory = CMemory::new().with_block("ordered", 4096);
        for (index, variable) in variables.iter().enumerate() {
            memory = memory.store(pointer(*variable, 4), int32(index as u32));
        }
        for at in [0, 4, 8] {
            let address = pointer(variables[at], 4);
            let fast = memory.without_possible_aliasing_cells(&address, 4, &context);
            let reference =
                crate::kernel::reasoning::store_gap::with_store_gap_skip_disabled(|| {
                    memory.without_possible_aliasing_cells(&address, 4, &context)
                });
            assert_eq!(fast, reference, "store at logical rank {at}");
        }
        let near = pointer(variables[3], 4);
        let wide = memory
            .without_possible_aliasing_cells(&near, 8, &context)
            .store(
                near.clone(),
                CValue::UInt64(Bitvector32Term::UInt64Constant(7)),
            );
        let after = wide.without_possible_aliasing_cells(&pointer(variables[4], 4), 4, &context);
        assert!(
            after.cells.get(&near).is_none(),
            "an eight-byte cell one index away may overlap"
        );
        let mixed = pointer(variables[0], 8);
        let mixed_memory = memory.store(mixed.clone(), int32(11));
        let after =
            mixed_memory.without_possible_aliasing_cells(&pointer(variables[8], 4), 4, &context);
        let reference = crate::kernel::reasoning::store_gap::with_store_gap_skip_disabled(|| {
            mixed_memory.without_possible_aliasing_cells(&pointer(variables[8], 4), 4, &context)
        });
        assert_eq!(after, reference, "mixed strides require ordinary checks");
    }
}
