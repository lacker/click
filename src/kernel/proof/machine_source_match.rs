//! Query-local structural matching of a selected machine source.
//!
//! Opaque native leaves use the existing native equality rule, but their
//! enclosing shared DAG is never exported. These keys are matching evidence,
//! not new term identities: the original typed operands and states survive.
use crate::kernel::*;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(Eq, PartialEq, Hash)]
enum Shape {
    Atom(KernelTerm),
    Fold(Variable, Variable, [usize; 4]),
    Match(AlgebraicTerm, Vec<(String, Vec<AlgebraicValue>, usize)>),
    If(ConditionTerm, [usize; 2]),
    Native(MachineTerm),
    Application(SharedPureApplication),
    Binary(MachineIntegerType, MachineBinaryOp, [usize; 2]),
    Unary(MachineIntegerType, MachineUnaryOp, usize),
    Cast(
        MachineCastSpelling,
        MachineIntegerType,
        MachineIntegerType,
        usize,
    ),
}
#[derive(Eq, PartialEq)]
struct Key(KernelType, Shape);
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Charge native payload hashing as well as shared-node visits. Only
        // selected opaque leaves use deep native keys, once per input node.
        struct Charged<'a, H>(&'a mut H);
        impl<H: Hasher> Hasher for Charged<'_, H> {
            fn finish(&self) -> u64 {
                self.0.finish()
            }
            fn write(&mut self, bytes: &[u8]) {
                crate::instrumentation::record_deterministic_work(bytes.len().div_ceil(8));
                self.0.write(bytes);
            }
        }
        let mut state = Charged(state);
        self.0.hash(&mut state);
        self.1.hash(&mut state);
    }
}

pub(in crate::kernel) struct MachineSourceMatcher<'a> {
    source: MachineOperandView<'a>,
    sources: HashMap<MachineIntegerType, KernelTerm>,
    nodes: HashMap<u64, usize>,
    keys: HashMap<Key, usize>,
}
impl<'a> MachineSourceMatcher<'a> {
    pub(in crate::kernel) fn new(source: MachineOperandView<'a>) -> Self {
        Self {
            source,
            sources: HashMap::new(),
            nodes: HashMap::new(),
            keys: HashMap::new(),
        }
    }

    pub(in crate::kernel) fn matches(
        &mut self,
        format: MachineIntegerType,
        term: &KernelTerm,
    ) -> Option<bool> {
        let source = self
            .sources
            .entry(format)
            .or_insert_with(|| KernelTerm::retained_machine_operand(format, self.source))
            .clone();
        Some(self.key(&source)? == self.key(term)?)
    }

    fn key(&mut self, root: &KernelTerm) -> Option<usize> {
        let mut pending = vec![(root, false)];
        while let Some((term, finish)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            if self.nodes.contains_key(&term.id()) {
                continue;
            }
            let children: Vec<_> = match term.node() {
                KernelTermNode::Match(matched) => matched.arguments[1..].iter().collect(),
                KernelTermNode::Fold(fold) => fold.arguments.iter().collect(),
                KernelTermNode::MachineIf { arguments } => arguments[1..].iter().collect(),
                KernelTermNode::MachineBinary { arguments, .. } => arguments.iter().collect(),
                KernelTermNode::MachineUnary { operand, .. }
                | KernelTermNode::MachineCast { operand, .. } => vec![operand],
                _ => Vec::new(),
            };
            if !finish && !children.is_empty() {
                pending.push((term, true));
                pending.extend(children.into_iter().map(|node| (node, false)));
                continue;
            }
            let shape = match term.node() {
                KernelTermNode::Match(matched) => {
                    let mut export = KernelTermExport::default();
                    let PureFunctionArgument::Algebraic(scrutinee) =
                        export.argument(&matched.arguments[0]).ok()?
                    else {
                        return None;
                    };
                    let arms = matched
                        .arms
                        .iter()
                        .zip(&matched.arguments[1..])
                        .map(|(arm, body)| {
                            Some((
                                arm.variant.clone(),
                                arm.export_bindings(&mut export).ok()?,
                                self.nodes[&body.id()],
                            ))
                        })
                        .collect::<Option<Vec<_>>>()?;
                    Shape::Match(scrutinee, arms)
                }
                KernelTermNode::Fold(fold) => Shape::Fold(
                    fold.accumulator,
                    fold.item,
                    fold.arguments
                        .each_ref()
                        .map(|child| self.nodes[&child.id()]),
                ),
                KernelTermNode::MachineIf { arguments } => Shape::If(
                    KernelTermExport::condition(&arguments[0]).ok()?,
                    [
                        self.nodes[&arguments[1].id()],
                        self.nodes[&arguments[2].id()],
                    ],
                ),
                KernelTermNode::MachineBinary {
                    format,
                    operator,
                    arguments,
                } => Shape::Binary(
                    *format,
                    *operator,
                    arguments.each_ref().map(|a| self.nodes[&a.id()]),
                ),
                KernelTermNode::MachineUnary {
                    format,
                    operator,
                    operand,
                } => Shape::Unary(*format, *operator, self.nodes[&operand.id()]),
                KernelTermNode::MachineCast {
                    encoding,
                    source,
                    destination,
                    operand,
                } => Shape::Cast(*encoding, *source, *destination, self.nodes[&operand.id()]),
                KernelTermNode::Legacy(_)
                | KernelTermNode::Call { .. }
                | KernelTermNode::BoolCast { .. } => {
                    let value = term
                        .machine_conversion_leaf()
                        .expect("retained native machine leaf");
                    if let MachineTerm::ClickFunctionApplication { name, arguments } = value {
                        Shape::Application(SharedPureApplication::intern(
                            name.clone(),
                            arguments.clone(),
                        ))
                    } else {
                        Shape::Native(value.clone())
                    }
                }
                _ => Shape::Atom(term.clone()),
            };
            let next = self.keys.len();
            let key = *self
                .keys
                .entry(Key(term.ty().clone(), shape))
                .or_insert(next);
            if crate::instrumentation::deadline_exceeded_with_work(0) {
                return None;
            }
            self.nodes.insert(term.id(), key);
        }
        Some(self.nodes[&root.id()])
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn boolean_cast_sources_keep_native_argument_equality() {
        let _session = VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(999464)),
            ProgramType::Int32Pointer,
        );
        let values = [pointer.clone(), pointer.with_pointee_constant(true)].map(|pointer| {
            MachineTerm::bool_cast(
                MachineIntegerType::Int32,
                ConditionTerm::BoolApplication(SharedPureApplication::intern(
                    "bool_source".into(),
                    vec![PureFunctionArgument::Value(ProgramValue::Pointer(pointer))],
                )),
            )
        });
        assert_eq!(values[0], values[1]);
        let root = KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &values[1])
            .unwrap();
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            MachineSourceMatcher::new(MachineOperandView::Legacy(&values[0]))
                .matches(MachineIntegerType::Int32, &root),
            Some(true)
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn selected_opaque_sources_keep_types_states_and_refusals() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(Memory::new().with_block("opaque-source", 16));
        let later = intern_memory(memory.memory().clone().with_block("later", 16));
        let pointer = Memory::global_pointer("opaque-source");
        let opaque = |memory: SharedMemory, name| MachineTerm::If {
            condition: ConditionTerm::Variable(Variable(name)).into(),
            then_term: MachineTerm::MemoryLoad(memory, pointer.clone().into(), LoadKind::Int32)
                .into(),
            else_term: MachineTerm::Variable(Variable(1006600)).into(),
        };
        let from = opaque(memory.clone(), 1006601);
        for ty in [MachineIntegerType::Int32, MachineIntegerType::UInt64] {
            let wrap = |v| MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: MachineIntegerType::Int32,
                to: ty,
                value: MachineTerm::add(v, MachineTerm::Variable(Variable(1006602))).into(),
            };
            let source = wrap(from.clone());
            for (candidate, expected) in [
                (wrap(from.clone()), true),
                (wrap(opaque(later.clone(), 1006601)), false),
                (wrap(opaque(memory.clone(), 1006603)), false),
            ] {
                let root = KernelTerm::retained_machine_operand(
                    ty,
                    MachineOperandView::Legacy(&candidate),
                );
                let exports = KernelTermExport::machine_export_count();
                let mut matcher = MachineSourceMatcher::new(MachineOperandView::Legacy(&source));
                assert_eq!(matcher.matches(ty, &root), Some(expected));
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                assert_eq!(KernelTermExport::machine(&root).unwrap(), candidate);
            }
        }
    }
}
