//! Exact boxed syntax of the arithmetic fragment retained by unsigned stores.
use super::*;

#[derive(Clone, Debug)]
pub(in crate::kernel) struct WordKey(Arc<WordKeyData>);

#[derive(Debug)]
struct WordKeyData {
    shape: WordShape,
    fingerprint: u64,
}

#[derive(Debug, Hash)]
enum WordShape {
    Leaf(MachineTerm),
    Binary {
        op: MachineBinaryOp,
        format: MachineIntegerType,
        children: [WordKey; 2],
    },
}

fn store_operator(format: MachineIntegerType, op: MachineBinaryOp) -> bool {
    matches!(
        format,
        MachineIntegerType::Int32 | MachineIntegerType::UInt32
    ) && matches!(
        op,
        MachineBinaryOp::Add | MachineBinaryOp::Subtract | MachineBinaryOp::Multiply
    )
}

impl WordKey {
    fn new(shape: WordShape) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        shape.hash(&mut hash);
        Self(Arc::new(WordKeyData {
            shape,
            fingerprint: hash.finish(),
        }))
    }

    pub(in crate::kernel) fn shared(root: &KernelTerm) -> Option<Self> {
        if !matches!(
            root.ty(),
            KernelType::Program(ProgramType::Int32 | ProgramType::UInt32)
        ) {
            return None;
        }
        Some(Self::new(match root.node() {
            KernelTermNode::Variable(v) => WordShape::Leaf(MachineTerm::Variable(*v)),
            KernelTermNode::MachineLiteral(v) => return Self::native(&v.legacy_term()),
            KernelTermNode::MachineBinary {
                format,
                operator,
                arguments,
            } if store_operator(*format, *operator) => WordShape::Binary {
                op: *operator,
                format: *format,
                children: [
                    arguments[0].word_storage_key()?.clone(),
                    arguments[1].word_storage_key()?.clone(),
                ],
            },
            _ => return None,
        }))
    }

    pub(in crate::kernel) fn native(value: &MachineTerm) -> Option<Self> {
        Some(Self::new(match value {
            MachineTerm::Variable(_)
            | MachineTerm::Constant {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                ..
            } => WordShape::Leaf(value.clone()),
            MachineTerm::Binary {
                op,
                format,
                left,
                right,
            } if store_operator(*format, *op) => WordShape::Binary {
                op: *op,
                format: *format,
                children: [Self::native(left)?, Self::native(right)?],
            },
            _ => return None,
        }))
    }

    fn rank(&self) -> u8 {
        match &self.0.shape {
            WordShape::Leaf(value) => native_machine_rank(value),
            WordShape::Binary { .. } => 2,
        }
    }

    pub(super) fn cmp_native(&self, other: &MachineTerm) -> Ordering {
        self.rank()
            .cmp(&native_machine_rank(other))
            .then_with(|| match (&self.0.shape, other) {
                (WordShape::Leaf(left), right) => left.cmp(right),
                (
                    WordShape::Binary {
                        op,
                        format,
                        children,
                    },
                    MachineTerm::Binary {
                        op: other_op,
                        format: other_format,
                        left,
                        right,
                    },
                ) => (*op, *format)
                    .cmp(&(*other_op, *other_format))
                    .then_with(|| children[0].cmp_native(left))
                    .then_with(|| children[1].cmp_native(right)),
                _ => unreachable!("matching word variant"),
            })
    }
}

impl Hash for WordKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.fingerprint.hash(state);
    }
}
impl PartialEq for WordKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.fingerprint == other.0.fingerprint && self.cmp(other).is_eq()
    }
}
impl Eq for WordKey {}
impl PartialOrd for WordKey {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for WordKey {
    fn cmp(&self, other: &Self) -> Ordering {
        let mut pending = vec![(self, other)];
        let mut seen = std::collections::HashSet::new();
        while let Some((a, b)) = pending.pop() {
            if Arc::ptr_eq(&a.0, &b.0) || !seen.insert((Arc::as_ptr(&a.0), Arc::as_ptr(&b.0))) {
                continue;
            }
            let order = a.rank().cmp(&b.rank());
            if !order.is_eq() {
                return order;
            }
            match (&a.0.shape, &b.0.shape) {
                (WordShape::Leaf(a), WordShape::Leaf(b)) => {
                    let order = a.cmp(b);
                    if !order.is_eq() {
                        return order;
                    }
                }
                (
                    WordShape::Binary {
                        op: a_op,
                        format: a_format,
                        children: a,
                    },
                    WordShape::Binary {
                        op: b_op,
                        format: b_format,
                        children: b,
                    },
                ) => {
                    let order = (a_op, a_format).cmp(&(b_op, b_format));
                    if !order.is_eq() {
                        return order;
                    }
                    pending.extend(a.iter().zip(b).rev());
                }
                _ => unreachable!("matching word variant"),
            }
        }
        Ordering::Equal
    }
}
