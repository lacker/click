//! Variable incidence without expanding a shared expression at every fact.
//!
//! Each syntax node retains its children and reverse parent edges. Facts attach
//! at roots. Two distinct downward witnesses suffice for singleton queries;
//! along a monotone branch each node accepts at most two witnesses. Enumeration
//! follows reverse edges once, returning the original facts in written order.
use super::*;
use crate::persistent::{PersistentMap, PersistentSet};

type Fact = SharedIndexFact<ConditionTerm>;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Key {
    Variable(Variable),
    Term(u64),
}
impl Key {
    fn of(term: &KernelTerm) -> Self {
        match term.node() {
            KernelTermNode::Variable(variable) => Self::Variable(*variable),
            _ => Self::Term(term.id()),
        }
    }
}
#[derive(Clone, Debug, Default)]
struct Node {
    children: Vec<Key>,
    parents: PersistentSet<Key>,
    facts: PersistentSet<Fact>,
    witnesses: Vec<Fact>,
}
#[derive(Clone, Debug)]
struct Source {
    roots: Vec<KernelTerm>,
    direct_variables: Option<Vec<Variable>>,
    value: bool,
}
#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct Index {
    nodes: PersistentMap<Key, Node>,
    sources: PersistentMap<Fact, Source>,
}
impl Index {
    /// This fragment's only dependencies are its written scalar variables.
    /// Registered reads retain the existing state/address-dependent index.
    fn source(condition: &ConditionTerm, truth: bool) -> Option<Source> {
        let crate::kernel::integer_comparison_condition!(left, right) = condition else {
            return None;
        };
        let mut roots = Vec::new();
        let mut direct_variables = BTreeSet::new();
        let mut shared = false;
        let mut has_variables = false;
        for value in [left.as_ref(), right.as_ref()] {
            match value {
                IntegerTerm::Constant(_) => {}
                IntegerTerm::Machine(value) => {
                    let root = match value.operand_view() {
                        MachineOperandView::Shared(root) => {
                            shared = true;
                            root.clone()
                        }
                        MachineOperandView::Legacy(MachineTerm::Variable(variable)) => {
                            KernelTerm::variable(
                                KernelType::Program(value.ty().program_type()),
                                *variable,
                            )
                        }
                        MachineOperandView::Legacy(value) if value.as_const().is_some() => continue,
                        _ => return None,
                    };
                    // Read addresses and states have their own dependency
                    // collector, just as registered read names did before.
                    if root.has_machine_reads() {
                        return None;
                    }
                    if !crate::kernel::shared_machine_conversion_leaves(&root, || {
                        crate::instrumentation::record_deterministic_work(1);
                        true
                    })?
                    .is_empty()
                    {
                        return None;
                    }
                    let variables = shared_machine_syntax_variables(&root, || {
                        crate::instrumentation::record_deterministic_work(1);
                        true
                    })?;
                    let loads = crate::kernel::eval::LOAD_VARIABLE_RANGE;
                    if variables
                        .get_greater_than(&Variable(loads.start - 1))
                        .is_some_and(|variable| variable.0 < loads.end)
                    {
                        return None;
                    }
                    // Three witnesses distinguish a bounded (at most two)
                    // dependency set without enumerating a large set.
                    direct_variables.extend(variables.iter().take(3).copied());
                    has_variables |= !variables.is_empty();
                    roots.push(root);
                }
                _ => return None,
            }
        }
        (shared && has_variables).then(|| {
            let direct =
                (direct_variables.len() <= 2).then(|| direct_variables.into_iter().collect());
            Source {
                roots,
                direct_variables: direct,
                value: truth,
            }
        })
    }

    fn install_root(&mut self, root: &KernelTerm) {
        let mut pending = vec![root];
        let mut new = Vec::new();
        while let Some(term) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let key = Key::of(term);
            if self.nodes.contains_key(&key) {
                continue;
            }
            let children: Vec<_> = term.children().iter().map(Key::of).collect();
            new.push((key, children.clone()));
            self.nodes.insert(
                key,
                Node {
                    children,
                    ..Default::default()
                },
            );
            pending.extend(term.children());
        }
        for (parent, children) in new {
            for child in children {
                let mut node = self.nodes.get(&child).unwrap().clone();
                node.parents = node.parents.with_value(parent);
                self.nodes.insert(child, node);
            }
        }
    }

    fn add_source(&mut self, fact: Fact, source: Source) {
        // A large DAG can mention only one or two variables. Attach such
        // sources directly: rebuilding syntax edges in every sibling branch
        // would repeatedly walk the same growing prefix. The bounded variable
        // summary is syntax-only; each branch still owns its facts/witnesses.
        let keys = if let Some(variables) = &source.direct_variables {
            variables
                .iter()
                .map(|variable| {
                    let key = Key::Variable(*variable);
                    if !self.nodes.contains_key(&key) {
                        self.nodes.insert(key, Node::default());
                    }
                    key
                })
                .collect::<Vec<_>>()
        } else {
            for root in &source.roots {
                self.install_root(root);
            }
            source.roots.iter().map(Key::of).collect()
        };
        let mut pending = Vec::new();
        for key in keys {
            let mut node = self.nodes.get(&key).unwrap().clone();
            node.facts = node.facts.with_value(fact.clone());
            self.nodes.insert(key, node);
            pending.push(key);
        }
        while let Some(key) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let mut node = self.nodes.get(&key).unwrap().clone();
            if node.witnesses.len() == 2 || node.witnesses.contains(&fact) {
                continue;
            }
            node.witnesses.push(fact.clone());
            pending.extend(node.children.iter().copied());
            self.nodes.insert(key, node);
        }
        self.sources.insert(fact, source);
    }

    pub(super) fn adjust(&mut self, condition: &ConditionTerm, value: bool) -> bool {
        if self.contains(condition) {
            return true;
        }
        let Some(source) = Self::source(condition, value) else {
            return false;
        };
        self.add_source(Fact::new(condition.clone()), source);
        true
    }
    pub(super) fn contains(&self, condition: &ConditionTerm) -> bool {
        self.sources.contains_key(condition)
    }
    pub(super) fn witnesses(
        &self,
        variable: Variable,
    ) -> impl Iterator<Item = (&ConditionTerm, bool)> {
        self.nodes
            .get(&Key::Variable(variable))
            .into_iter()
            .flat_map(|node| node.witnesses.iter())
            .map(|fact| (fact.as_ref(), self.sources.get(fact).unwrap().value))
    }
    pub(super) fn facts(&self, variable: Variable) -> BTreeMap<&ConditionTerm, bool> {
        let mut pending = vec![Key::Variable(variable)];
        let mut seen = BTreeSet::new();
        let mut facts = BTreeMap::new();
        while let Some(key) = pending.pop() {
            if !seen.insert(key) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let Some(node) = self.nodes.get(&key) else {
                continue;
            };
            pending.extend(node.parents.iter().copied());
            for fact in node.facts.iter() {
                crate::instrumentation::record_deterministic_work(1);
                facts.insert(fact.as_ref(), self.sources.get(fact).unwrap().value);
            }
        }
        facts
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variable(n: u64) -> KernelTerm {
        KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(n))
    }
    fn product(a: KernelTerm, b: KernelTerm) -> KernelTerm {
        KernelTerm::machine_binary_shared(
            MachineIntegerType::Int32,
            MachineBinaryOp::Multiply,
            [a, b],
        )
    }
    fn bound(root: KernelTerm, n: i64) -> ConditionTerm {
        ConditionTerm::integer_less_equal(
            IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap(),
            ),
            IntegerTerm::constant_i64(n),
        )
    }
    #[test]
    fn shared_adjacency_matches_variable_collection_and_keeps_branch_sources() {
        let _session = crate::kernel::VerificationSession::enter();
        let xy = product(variable(994700), variable(994701));
        let first = bound(xy.clone(), 7);
        let second = bound(product(xy.clone(), variable(994702)), 8);
        let third = bound(product(xy.clone(), xy), 9);
        let native = ConditionTerm::signed_less_equal(
            MachineTerm::Variable(Variable(994700)),
            MachineTerm::constant(10),
        );
        let parent = PureFactContext::new().assume_condition(first.clone(), true);
        assert_eq!(
            parent.singleton_condition_variable(Variable(994700)),
            Some((&first, true))
        );
        let branch = parent
            .clone()
            .assume_condition(second.clone(), false)
            .assume_condition(third.clone(), true)
            .assume_condition(native.clone(), true);
        let sources = [
            (&first, true),
            (&second, false),
            (&third, true),
            (&native, true),
        ];
        for id in 994700..994704 {
            let variable = Variable(id);
            let expected: BTreeMap<_, _> = sources.into_iter().filter(|(condition, _)| {
                let mut variables = BTreeSet::new();
                assert!(!crate::kernel::reasoning::variable_collection::collect_condition_index_variables(condition, &mut variables));
                variables.contains(&variable)
            }).collect();
            assert_eq!(
                branch
                    .condition_variable_facts(variable)
                    .collect::<BTreeMap<_, _>>(),
                expected
            );
            let selected: BTreeMap<_, _> = branch
                .condition_facts_mentioning_variable(variable)
                .unwrap()
                .collect();
            assert_eq!(selected, expected);
            let singleton = (expected.len() == 1)
                .then(|| expected.iter().next().map(|(c, v)| (*c, *v)))
                .flatten();
            assert_eq!(branch.singleton_condition_variable(variable), singleton);
            assert_eq!(
                branch.has_condition_variable(variable),
                !expected.is_empty()
            );
            let key = AtomicConnectionKey::Variable(variable);
            let (connected, _) = branch.atomic_facts_connected_to(&key, true);
            let connected: BTreeMap<_, _> = connected
                .filter_map(|fact| match fact {
                    AtomicConnectedFact::Condition(condition, value) => Some((condition, value)),
                    _ => None,
                })
                .collect();
            assert_eq!(connected, expected);
        }
        assert_eq!(
            parent.singleton_condition_variable(Variable(994700)),
            Some((&first, true))
        );
        assert!(!parent.has_condition_variable(Variable(994702)));
    }

    #[test]
    fn shared_roots_keep_native_and_load_dependent_sources_in_the_existing_index() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(Memory::new());
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Pointer::symbolic(Variable(994800)),
            LoadKind::Int32,
            4,
        );
        let condition = bound(product(variable(load.0), variable(994801)), 7);
        let facts = PureFactContext::new().assume_condition(condition.clone(), true);
        assert!(!facts.shared_condition_variables.contains(&condition));
        assert!(
            facts
                .condition_facts_mentioning_variable(Variable(994800))
                .unwrap()
                .any(|(c, v)| c == &condition && v)
        );
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/assumptions/shared_condition_variables.rs");
    }
}
