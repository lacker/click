//! Structural correspondence of shared operands. Cache only syntax and the
//! read/variable leaf pairs left to check; registry lookups and proof authority stay
//! with the caller and are never cached here.
use super::*;
use crate::persistent::PersistentMap;

#[derive(Clone, Copy, Eq, PartialEq, Hash)]
enum CorrespondencePolicy {
    LoadAtoms,
    ConditionLoads,
    // Only a 32-bit ring-operator path may frame changed read states.
    MemoryState(bool),
}

type Key = (MachineIntegerType, CorrespondencePolicy, u64, u64);
type Pairs = PersistentMap<(u64, u64), (KernelTerm, KernelTerm)>;
thread_local! {
    static PAIRS: std::cell::RefCell<HashMap<Key, Option<Pairs>>> = Default::default();
}

pub(super) fn clear() {
    PAIRS.with(|pairs| pairs.borrow_mut().clear());
}

pub(crate) fn shared_operand_leaf_pairs(
    format: MachineIntegerType,
    left: &KernelTerm,
    right: &KernelTerm,
) -> Option<Pairs> {
    shared_operand_leaf_pairs_with_policy(format, left, right, CorrespondencePolicy::LoadAtoms)
}

/// Selected condition matching also returns differing guards for the caller's
/// load authority. These are syntax pairs, never cached proof decisions.
pub(crate) fn shared_condition_operand_leaf_pairs(
    format: MachineIntegerType,
    left: &KernelTerm,
    right: &KernelTerm,
) -> Option<Pairs> {
    shared_operand_leaf_pairs_with_policy(format, left, right, CorrespondencePolicy::ConditionLoads)
}

pub(crate) fn shared_state_read_pairs(left: &KernelTerm, right: &KernelTerm) -> Option<Pairs> {
    shared_operand_leaf_pairs_with_policy(
        MachineIntegerType::Int32,
        left,
        right,
        CorrespondencePolicy::MemoryState(true),
    )
}

/// Exact native syntax equality for retained machine DAGs. No read framing,
/// registry resolution, constant evaluation, or premise lookup is permitted.
pub(crate) fn shared_machine_syntax_equal(left: &KernelTerm, right: &KernelTerm) -> bool {
    shared_operand_leaf_pairs_with_policy(
        MachineIntegerType::Int32,
        left,
        right,
        CorrespondencePolicy::MemoryState(false),
    )
    .is_some()
}

fn shared_operand_leaf_pairs_with_policy(
    format: MachineIntegerType,
    left: &KernelTerm,
    right: &KernelTerm,
    policy: CorrespondencePolicy,
) -> Option<Pairs> {
    use CorrespondencePolicy as P;
    use MachineOperandView::Shared as V;
    // End the borrow before a caller checks the returned load pairs: that
    // check can itself ask a structural comparison question.
    PAIRS.with(|pairs| {
        let mut pairs = pairs.borrow_mut();
        let mut pending = vec![(format, policy, left, right, false)];
        while let Some((format, policy, left, right, finish)) = pending.pop() {
            let key = (format, policy, left.id(), right.id());
            if pairs.contains_key(&key) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            if left == right {
                pairs.insert(key, Some(Pairs::default()));
                continue;
            }
            // Exact retained inputs can have different producer identities
            // to preserve metadata. Numeric syntax equality relates their
            // values without replacing either payload or consulting facts.
            if let (Some(a), Some(b)) = (
                left.machine_conversion_leaf(),
                right.machine_conversion_leaf(),
            ) {
                let equal = a == b
                    || match (a, b) {
                        (
                            MachineTerm::ClickFunctionApplication {
                                name: an,
                                arguments: aa,
                            },
                            MachineTerm::ClickFunctionApplication {
                                name: bn,
                                arguments: ba,
                            },
                        ) if an == bn => {
                            SharedPureApplication::intern(an.clone(), aa.clone())
                                == SharedPureApplication::intern(bn.clone(), ba.clone())
                        }
                        _ => false,
                    };
                pairs.insert(key, equal.then(Pairs::default));
                continue;
            }
            let (a, b) = (V(left), V(right));
            if a.fold().is_some()
                || b.fold().is_some()
                || a.matched().is_some()
                || b.matched().is_some()
            {
                pairs.insert(
                    key,
                    machine_operand_syntax_cmp(a, b)
                        .is_eq()
                        .then(Pairs::default),
                );
                continue;
            }
            if (a.variable().is_some() || a.read().is_some())
                && (b.variable().is_some() || b.read().is_some())
            {
                let result = if let P::MemoryState(frame) = policy {
                    let a_source = a.read_source().expect("selected atom");
                    let b_source = b.read_source().expect("selected atom");
                    if a_source == b_source {
                        Some(Pairs::default())
                    } else if frame && a.read().is_some() && b.read().is_some() {
                        Some(
                            Pairs::default().with_inserted(
                                (left.id(), right.id()),
                                (left.clone(), right.clone()),
                            ),
                        )
                    } else {
                        None
                    }
                } else {
                    Some(
                        Pairs::default()
                            .with_inserted((left.id(), right.id()), (left.clone(), right.clone())),
                    )
                };
                pairs.insert(key, result);
                continue;
            }
            if let (Some(a), Some(b)) = (a.literal(), b.literal()) {
                if matches!(policy, P::MemoryState(_)) {
                    pairs.insert(key, (a == b).then(Pairs::default));
                    continue;
                }
                let a = format.constant_from_term(&a);
                let b = format.constant_from_term(&b);
                pairs.insert(
                    key,
                    a.zip(b)
                        .filter(|(a, b)| a.bits() == b.bits())
                        .map(|_| Pairs::default()),
                );
                continue;
            }
            let children = if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
                (a.binary(), b.binary())
            {
                let child_policy = match policy {
                    P::MemoryState(frame) => P::MemoryState(
                        frame
                            && af.format().bits() == 32
                            && matches!(
                                ao,
                                crate::kernel::MachineBinaryOp::Add
                                    | crate::kernel::MachineBinaryOp::Subtract
                                    | crate::kernel::MachineBinaryOp::Multiply
                            ),
                    ),
                    P::LoadAtoms | P::ConditionLoads => policy,
                };
                (af == bf && ao == bo)
                    .then_some(vec![(af, child_policy, al, bl), (af, child_policy, ar, br)])
            } else if let (Some((af, ao, av)), Some((bf, bo, bv))) = (a.unary(), b.unary()) {
                (af == bf && ao == bo).then_some(vec![(
                    af,
                    match policy {
                        P::MemoryState(_) => P::MemoryState(false),
                        P::LoadAtoms | P::ConditionLoads => policy,
                    },
                    av,
                    bv,
                )])
            } else if let (Some((ae, af, at, av)), Some((be, bf, bt, bv))) = (a.cast(), b.cast()) {
                (ae == be && af == bf && at == bt).then_some(vec![(
                    af,
                    match policy {
                        P::MemoryState(_) => P::MemoryState(false),
                        P::LoadAtoms | P::ConditionLoads => policy,
                    },
                    av,
                    bv,
                )])
            } else if let (Some((ac, [al, ar])), Some((bc, [bl, br]))) =
                (a.conditional_view(), b.conditional_view())
            {
                let child_policy = if matches!(policy, P::ConditionLoads) {
                    policy
                } else {
                    P::MemoryState(false)
                };
                (matches!(policy, P::ConditionLoads) || ac.syntax_equal(bc)).then_some(vec![
                    (format, child_policy, al, bl),
                    (format, child_policy, ar, br),
                ])
            } else {
                None
            };
            let Some(children) = children else {
                pairs.insert(key, None);
                continue;
            };
            let children: Vec<_> = children
                .into_iter()
                .map(|(format, policy, a, b)| {
                    let (V(a), V(b)) = (a, b) else {
                        unreachable!("shared children");
                    };
                    (format, policy, a, b)
                })
                .collect();
            if !finish {
                pending.push((format, policy, left, right, true));
                pending.extend(children.into_iter().map(|(f, p, a, b)| (f, p, a, b, false)));
                continue;
            }
            let mut initial = Pairs::default();
            if matches!(policy, P::ConditionLoads)
                && let (
                    KernelTermNode::MachineIf { arguments: a },
                    KernelTermNode::MachineIf { arguments: b },
                ) = (left.node(), right.node())
                && a[0] != b[0]
            {
                initial =
                    initial.with_inserted((a[0].id(), b[0].id()), (a[0].clone(), b[0].clone()));
            }
            let mut result = Some(initial);
            for (format, child_policy, a, b) in children {
                let Some(child) = &pairs[&(format, child_policy, a.id(), b.id())] else {
                    result = None;
                    break;
                };
                let current = result.as_mut().expect("matching prefix");
                if current.shares_root_with(child) {
                    continue;
                }
                let (large, small) = if current.len() >= child.len() {
                    (&*current, child)
                } else {
                    (child, &*current)
                };
                let mut combined = large.clone();
                for (key, pair) in small.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    combined = combined.with_inserted(*key, pair.clone());
                }
                *current = combined;
            }
            pairs.insert(key, result);
        }
        pairs[&(format, policy, left.id(), right.id())].clone()
    })
}

/// Native syntax order over retained operands. Used only where an existing
/// explicit candidate list promises native ordering; never as a hot index key.
pub(crate) fn machine_operand_syntax_cmp(
    left: MachineOperandView<'_>,
    right: MachineOperandView<'_>,
) -> std::cmp::Ordering {
    use MachineOperandView as V;
    use std::cmp::Ordering;
    fn header(view: V<'_>) -> MachineTerm {
        let zero = || Box::new(MachineTerm::constant(0));
        if view.conditional_view().is_some() {
            MachineTerm::If {
                condition: Box::new(ConditionTerm::Constant(false)),
                then_term: zero(),
                else_term: zero(),
            }
        } else if let Some(matched) = view.matched() {
            MachineTerm::AlgebraicMatch {
                scrutinee: Box::new(matched.scrutinee.into_owned()),
                arms: vec![],
            }
        } else if view.fold().is_some() {
            MachineTerm::RangeFold {
                start: zero(),
                end: zero(),
                initial: zero(),
                accumulator: Variable(0),
                item: Variable(0),
                body: zero(),
            }
        } else if let Some((format, op, _)) = view.binary() {
            MachineTerm::Binary {
                format,
                op,
                left: zero(),
                right: zero(),
            }
        } else if let Some((format, op, _)) = view.unary() {
            MachineTerm::Unary {
                format,
                op,
                operand: zero(),
            }
        } else if let Some((spelling, from, to, _)) = view.cast() {
            MachineTerm::Cast {
                spelling,
                from,
                to,
                value: zero(),
            }
        } else {
            view.literal().unwrap_or_else(|| {
                view.read_source()
                    .expect("retained native leaf")
                    .into_owned()
            })
        }
    }
    enum Task<'a, 'b> {
        Pair(V<'a>, V<'b>),
        Order(Ordering),
    }
    let mut pending = vec![Task::Pair(left, right)];
    let mut seen = std::collections::HashSet::new();
    while let Some(task) = pending.pop() {
        let (a, b) = match task {
            Task::Order(order) if !order.is_eq() => return order,
            Task::Order(_) => continue,
            Task::Pair(a, b) => (a, b),
        };
        crate::instrumentation::record_deterministic_work(1);
        if let (V::Legacy(a), V::Legacy(b)) = (a, b) {
            let order = a.cmp(b);
            if !order.is_eq() {
                return order;
            }
            continue;
        }
        if let (V::Shared(a), V::Shared(b)) = (a, b) {
            if a == b || !seen.insert((a.id(), b.id())) {
                continue;
            }
        }
        if let (Some((ag, [at, ae])), Some((bg, [bt, be]))) = (a.conditional(), b.conditional()) {
            let order = ag.cmp(&bg);
            if !order.is_eq() {
                return order;
            }
            pending.push(Task::Pair(ae, be));
            pending.push(Task::Pair(at, bt));
            continue;
        }
        if let (Some(a), Some(b)) = (a.matched(), b.matched()) {
            let order = a.scrutinee.cmp(&b.scrutinee);
            if !order.is_eq() {
                return order;
            }
            pending.push(Task::Order(a.arms.len().cmp(&b.arms.len())));
            for (a, b) in a.arms.iter().zip(&b.arms).rev() {
                pending.push(Task::Pair(a.body, b.body));
                pending.push(Task::Order(
                    a.variant.cmp(b.variant).then(a.bindings.cmp(&b.bindings)),
                ));
            }
            continue;
        }
        if let (Some((aa, ai, ac)), Some((ba, bi, bc))) = (a.fold(), b.fold()) {
            // Native field order: bounds, initial, binder identities, body.
            pending.push(Task::Pair(ac[3], bc[3]));
            pending.push(Task::Order(aa.cmp(&ba).then(ai.cmp(&bi))));
            for i in (0..3).rev() {
                pending.push(Task::Pair(ac[i], bc[i]));
            }
            continue;
        }
        if let (Some((ae, af, at, av)), Some((be, bf, bt, bv))) = (a.cast(), b.cast()) {
            let order = ae.cmp(&be);
            if !order.is_eq() {
                return order;
            }
            pending.push(Task::Order(af.cmp(&bf).then(at.cmp(&bt))));
            pending.push(Task::Pair(av, bv));
            continue;
        }
        let order = header(a).cmp(&header(b));
        if !order.is_eq() {
            return order;
        }
        if let (Some((_, _, [al, ar])), Some((_, _, [bl, br]))) = (a.binary(), b.binary()) {
            pending.push(Task::Pair(ar, br));
            pending.push(Task::Pair(al, bl));
        } else if let (Some((_, _, av)), Some((_, _, bv))) = (a.unary(), b.unary()) {
            pending.push(Task::Pair(av, bv));
        }
    }
    Ordering::Equal
}
