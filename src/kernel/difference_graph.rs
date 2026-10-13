//! Difference logic over the path's integer facts: a persistent graph of
//! constraints `x - y <= c` with a constant interval on every node, extended
//! fact by fact and queried by reading bounds and edges.
//!
//! Nodes are `(domain, term)` pairs whose values are mathematical integers,
//! so values of different widths can be related. A constant is never a node:
//! a bound `x <= 4` narrows `x`'s interval instead of joining `x` to a node
//! `4`, so facts about unrelated values never meet at a shared constant. A
//! term `x + k` is linked to `x` only once `x`'s interval shows the sum
//! cannot wrap in its domain.
//!
//! Insertion checks the new edge for a negative cycle among the nodes it
//! reaches, then propagates intervals from the edge's endpoints. Its work
//! is the component the edge joins, not the graph. A query compares stored
//! intervals and, between two nodes, reads the shortest path inside the
//! source's component. Every answer follows from the inserted facts by
//! difference logic; a contradictory graph answers nothing.
//!
//! See `issues/difference-logic.md`.

use crate::kernel::{Bitvector32Term, ConditionTerm};
use crate::persistent::PersistentMap;

/// The integer domain a node's value ranges over.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Domain {
    Int32,
    Int64,
    UInt64,
}

impl Domain {
    fn range(self) -> (i128, i128) {
        match self {
            Domain::Int32 => (i128::from(i32::MIN), i128::from(i32::MAX)),
            Domain::Int64 => (i128::from(i64::MIN), i128::from(i64::MAX)),
            Domain::UInt64 => (0, i128::from(u64::MAX)),
        }
    }
}

type NodeId = u32;

/// A value as `node + offset`, or the constant `offset` when `node` is
/// `None`.
type Affine = (Option<NodeId>, i128);

/// A link a node waits for: `node = base + offset` once `base`'s interval
/// shows the value stays in `domain` (and is non-negative, for a conversion
/// that keeps only non-negative values).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PendingLink {
    offset: i128,
    domain: Domain,
    nonnegative: bool,
}

#[derive(Clone, Default)]
pub(crate) struct DifferenceGraph {
    nodes: PersistentMap<(Domain, Bitvector32Term), NodeId>,
    domains: PersistentMap<NodeId, Domain>,
    /// Tightened intervals; a node absent here ranges over its domain.
    bounds: PersistentMap<NodeId, (i128, i128)>,
    /// `from -> to -> w`: `to - from <= w`, the least `w` inserted.
    out_edges: PersistentMap<NodeId, PersistentMap<NodeId, i128>>,
    in_edges: PersistentMap<NodeId, PersistentMap<NodeId, i128>>,
    /// `base -> node -> link`: links waiting on `base`'s interval.
    pending: PersistentMap<NodeId, PersistentMap<NodeId, PendingLink>>,
    contradictory: bool,
    next: NodeId,
}

/// Charges and, in test builds, counts one unit of graph work.
fn charge() {
    crate::instrumentation::record_deterministic_work(1);
    #[cfg(test)]
    tests::GRAPH_WORK.with(|work| work.set(work.get() + 1));
}

impl DifferenceGraph {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Whether the inserted facts contradict each other.
    pub(crate) fn is_contradictory(&self) -> bool {
        self.contradictory
    }

    fn domain(&self, node: NodeId) -> Domain {
        *self.domains.get(&node).expect("a node has a domain")
    }

    fn interval(&self, node: NodeId) -> (i128, i128) {
        self.bounds
            .get(&node)
            .copied()
            .unwrap_or_else(|| self.domain(node).range())
    }

    fn affine_interval(&self, (node, offset): Affine) -> (i128, i128) {
        match node {
            None => (offset, offset),
            Some(node) => {
                let (low, high) = self.interval(node);
                (low + offset, high + offset)
            }
        }
    }

    /// Records a true or false condition fact. A fact difference logic does
    /// not express is ignored.
    pub(crate) fn assume_condition(&mut self, condition: &ConditionTerm, value: bool) {
        for (domain, lower, upper, strict) in condition_orders(condition, value) {
            if self.contradictory {
                return;
            }
            let lower = self.affine(domain, &lower);
            let upper = self.affine(domain, &upper);
            // lower - upper <= -strict
            self.constrain(upper, lower, -i128::from(strict));
        }
    }

    /// `to - from <= weight`.
    fn constrain(&mut self, from: Affine, to: Affine, weight: i128) {
        // (to.node + to.offset) - (from.node + from.offset) <= weight
        let weight = weight - to.1 + from.1;
        match (from.0, to.0) {
            (None, None) => {
                if 0 > weight {
                    self.contradictory = true;
                }
            }
            (None, Some(to)) => self.tighten(to, None, Some(weight)),
            (Some(from), None) => self.tighten(from, Some(-weight), None),
            (Some(from), Some(to)) if from == to => {
                if weight < 0 {
                    self.contradictory = true;
                }
            }
            (Some(from), Some(to)) => self.add_edge(from, to, weight),
        }
    }

    fn add_edge(&mut self, from: NodeId, to: NodeId, weight: i128) {
        if self
            .out_edges
            .get(&from)
            .and_then(|edges| edges.get(&to))
            .is_some_and(|existing| *existing <= weight)
        {
            return;
        }
        // A path `to -> from` shorter than `-weight` closes a negative cycle.
        if self
            .shortest_from(to)
            .get(&from)
            .is_some_and(|distance| distance + weight < 0)
        {
            self.contradictory = true;
            return;
        }
        let out = self.out_edges.get(&from).cloned().unwrap_or_default();
        self.out_edges.insert(from, out.with_inserted(to, weight));
        let incoming = self.in_edges.get(&to).cloned().unwrap_or_default();
        self.in_edges
            .insert(to, incoming.with_inserted(from, weight));
        let (_, from_high) = self.interval(from);
        let (to_low, _) = self.interval(to);
        self.tighten(to, None, Some(from_high.saturating_add(weight)));
        self.tighten(from, Some(to_low.saturating_sub(weight)), None);
    }

    /// Narrows `node`'s interval and propagates along its edges: a lower
    /// upper bound flows forward (`m - n <= w` bounds `m <= hi(n) + w`), a
    /// higher lower bound backward (`n - p <= w` bounds `p >= lo(n) - w`).
    fn tighten(&mut self, node: NodeId, low: Option<i128>, high: Option<i128>) {
        let mut work = vec![(node, low, high)];
        while let Some((node, low, high)) = work.pop() {
            if self.contradictory {
                return;
            }
            charge();
            let (old_low, old_high) = self.interval(node);
            let new_low = low.map_or(old_low, |low| low.max(old_low));
            let new_high = high.map_or(old_high, |high| high.min(old_high));
            if (new_low, new_high) == (old_low, old_high) {
                continue;
            }
            if new_low > new_high {
                self.contradictory = true;
                return;
            }
            self.bounds.insert(node, (new_low, new_high));
            if new_high < old_high
                && let Some(edges) = self.out_edges.get(&node)
            {
                for (next, weight) in edges.iter() {
                    work.push((*next, None, Some(new_high.saturating_add(*weight))));
                }
            }
            if new_low > old_low
                && let Some(edges) = self.in_edges.get(&node)
            {
                for (previous, weight) in edges.iter() {
                    work.push((*previous, Some(new_low.saturating_sub(*weight)), None));
                }
            }
            self.resolve_pending(node);
        }
    }

    /// Adds every link waiting on `base` whose value now provably stays in
    /// its domain.
    fn resolve_pending(&mut self, base: NodeId) {
        let Some(waiting) = self.pending.get(&base).cloned() else {
            return;
        };
        let (low, high) = self.interval(base);
        let mut remaining = waiting.clone();
        let mut linked = Vec::new();
        for (node, link) in waiting.iter() {
            charge();
            let (min, max) = link.domain.range();
            let fits = if link.nonnegative {
                low >= 0 && high <= max
            } else {
                low + link.offset >= min && high + link.offset <= max
            };
            if fits {
                remaining = remaining.without_key(node);
                linked.push((*node, link.offset));
            }
        }
        if remaining.is_empty() {
            self.pending.remove(&base);
        } else {
            self.pending.insert(base, remaining);
        }
        for (node, offset) in linked {
            // node = base + offset
            self.constrain((Some(base), 0), (Some(node), 0), offset);
            self.constrain((Some(node), 0), (Some(base), 0), -offset);
        }
    }

    /// Shortest distances from `source` over the edges it reaches
    /// (`distance[v]` bounds `v - source`). The caller has excluded negative
    /// cycles, so the relaxation terminates.
    fn shortest_from(&self, source: NodeId) -> std::collections::BTreeMap<NodeId, i128> {
        let mut distance = std::collections::BTreeMap::from([(source, 0i128)]);
        // First in, first out: with negative weights a stack can revisit a
        // node exponentially often; a queue relaxes in rounds.
        let mut work = std::collections::VecDeque::from([source]);
        while let Some(node) = work.pop_front() {
            let Some(edges) = self.out_edges.get(&node) else {
                continue;
            };
            let base = distance[&node];
            for (next, weight) in edges.iter() {
                charge();
                let candidate = base + weight;
                if distance.get(next).is_none_or(|known| candidate < *known) {
                    distance.insert(*next, candidate);
                    work.push_back(*next);
                }
            }
        }
        distance
    }

    /// The node for `term`, created with its pending links when new.
    fn node(&mut self, domain: Domain, term: &Bitvector32Term) -> NodeId {
        if let Some(node) = self.nodes.get(&(domain, term.clone())) {
            return *node;
        }
        let node = self.next;
        self.next += 1;
        self.nodes.insert((domain, term.clone()), node);
        self.domains.insert(node, domain);
        if let Some((base_domain, base, offset, nonnegative)) = link_parts(domain, term) {
            let base = self.affine(base_domain, base);
            match base {
                (None, constant) => {
                    // A constant base: the value is known when it fits.
                    let (min, max) = domain.range();
                    let value = constant + offset;
                    if value >= min && value <= max && (!nonnegative || constant >= 0) {
                        self.tighten(node, Some(value), Some(value));
                    }
                }
                (Some(base_node), base_offset) => {
                    let waiting = self.pending.get(&base_node).cloned().unwrap_or_default();
                    self.pending.insert(
                        base_node,
                        waiting.with_inserted(
                            node,
                            PendingLink {
                                offset: offset + base_offset,
                                domain,
                                nonnegative,
                            },
                        ),
                    );
                    self.resolve_pending(base_node);
                }
            }
        }
        node
    }

    fn affine(&mut self, domain: Domain, term: &Bitvector32Term) -> Affine {
        match constant(domain, term) {
            Some(value) => (None, value),
            None => (Some(self.node(domain, term)), 0),
        }
    }

    /// `term` as known nodes and constants, without adding to the graph.
    /// A term not in the graph resolves through a link its base's interval
    /// already justifies; otherwise `None`.
    fn resolve(&self, domain: Domain, term: &Bitvector32Term) -> Option<Affine> {
        if let Some(value) = constant(domain, term) {
            return Some((None, value));
        }
        if let Some(node) = self.nodes.get(&(domain, term.clone())) {
            return Some((Some(*node), 0));
        }
        let (base_domain, base, offset, nonnegative) = link_parts(domain, term)?;
        let base = self.resolve(base_domain, base)?;
        let (low, high) = self.affine_interval(base);
        let (min, max) = domain.range();
        let fits = if nonnegative {
            low >= 0 && high <= max
        } else {
            low + offset >= min && high + offset <= max
        };
        fits.then_some((base.0, base.1 + offset))
    }

    /// The least known upper bound on `to - from`, from intervals and from
    /// the shortest path inside `from`'s component.
    fn difference_bound(&self, from: Affine, to: Affine) -> i128 {
        let (_, to_high) = self.affine_interval(to);
        let (from_low, _) = self.affine_interval(from);
        let by_intervals = to_high - from_low;
        let by_path = match (from.0, to.0) {
            (Some(from_node), Some(to_node)) => self
                .shortest_from(from_node)
                .get(&to_node)
                .map(|distance| distance + to.1 - from.1),
            _ => None,
        };
        by_path.map_or(by_intervals, |path| path.min(by_intervals))
    }

    /// What the inserted facts decide about `condition`: its truth value,
    /// or `None` when difference logic leaves it open or the facts are
    /// contradictory.
    pub(crate) fn decide(&self, condition: &ConditionTerm) -> Option<bool> {
        use ConditionTerm as C;
        if self.contradictory {
            return None;
        }
        if let C::Constant(value) = condition {
            return Some(*value);
        }
        let overflow = match condition {
            C::Bitvector32SignedAddOverflows(a, b) => Some((Domain::Int32, a, b, Operation::Add)),
            C::Bitvector32SignedSubtractOverflows(a, b) => {
                Some((Domain::Int32, a, b, Operation::Subtract))
            }
            C::Bitvector32SignedMultiplyOverflows(a, b) => {
                Some((Domain::Int32, a, b, Operation::Multiply))
            }
            C::Bitvector64SignedAddOverflows(a, b) => Some((Domain::Int64, a, b, Operation::Add)),
            C::Bitvector64SignedSubtractOverflows(a, b) => {
                Some((Domain::Int64, a, b, Operation::Subtract))
            }
            C::Bitvector64SignedMultiplyOverflows(a, b) => {
                Some((Domain::Int64, a, b, Operation::Multiply))
            }
            _ => None,
        };
        if let Some((domain, a, b, operation)) = overflow {
            return self.decide_overflow(domain, a, b, operation);
        }
        if let C::Bitvector32Equal(a, b) | C::Bitvector64Equal(a, b) = condition {
            let domains: &[Domain] = if matches!(condition, C::Bitvector32Equal(..)) {
                &[Domain::Int32]
            } else {
                &[Domain::Int64, Domain::UInt64]
            };
            for domain in domains {
                let (Some(a), Some(b)) = (self.resolve(*domain, a), self.resolve(*domain, b))
                else {
                    continue;
                };
                let ab = self.difference_bound(a, b);
                let ba = self.difference_bound(b, a);
                if ab <= 0 && ba <= 0 {
                    return Some(true);
                }
                if ab < 0 || ba < 0 {
                    return Some(false);
                }
            }
            return None;
        }
        let [(domain, ref lower, ref upper, strict)] = condition_orders(condition, true)[..] else {
            return None;
        };
        let lower = self.resolve(domain, lower)?;
        let upper = self.resolve(domain, upper)?;
        // lower < upper (or <=) holds when lower - upper <= -strict, and
        // fails when upper - lower <= -(not strict).
        if self.difference_bound(upper, lower) <= -i128::from(strict) {
            return Some(true);
        }
        if self.difference_bound(lower, upper) <= -i128::from(!strict) {
            return Some(false);
        }
        None
    }

    /// Whether `a op b` leaves `domain`, from the operands' intervals and,
    /// for a subtraction of two nodes, the difference between them. An
    /// operand the graph cannot resolve ranges over its domain.
    fn decide_overflow(
        &self,
        domain: Domain,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
        operation: Operation,
    ) -> Option<bool> {
        let a = self.resolve(domain, a);
        let b = self.resolve(domain, b);
        let interval = |affine: Option<Affine>| {
            affine.map_or_else(|| domain.range(), |affine| self.affine_interval(affine))
        };
        let (a_low, a_high) = interval(a);
        let (b_low, b_high) = interval(b);
        let (low, high) = match operation {
            Operation::Add => (a_low + b_low, a_high + b_high),
            Operation::Subtract => {
                let mut high = a_high - b_low;
                let mut low = a_low - b_high;
                if let (Some(a), Some(b)) = (a, b) {
                    high = high.min(self.difference_bound(b, a));
                    low = low.max(-self.difference_bound(a, b));
                }
                (low, high)
            }
            Operation::Multiply => {
                let products = [
                    a_low * b_low,
                    a_low * b_high,
                    a_high * b_low,
                    a_high * b_high,
                ];
                (*products.iter().min()?, *products.iter().max()?)
            }
        };
        let (min, max) = domain.range();
        if low >= min && high <= max {
            Some(false)
        } else if low > max || high < min {
            Some(true)
        } else {
            None
        }
    }
}

#[derive(Clone, Copy)]
enum Operation {
    Add,
    Subtract,
    Multiply,
}

/// `term`'s value in `domain` when it is a constant there.
fn constant(domain: Domain, term: &Bitvector32Term) -> Option<i128> {
    use Bitvector32Term as T;
    match (domain, term) {
        (Domain::Int32, T::Constant(value)) => Some(i128::from(*value as i32)),
        (Domain::Int64, T::Int64Constant(value)) => Some(i128::from(*value)),
        (Domain::UInt64, T::UInt64Constant(value)) => Some(i128::from(*value)),
        (Domain::UInt64, T::Int64Constant(value)) if *value >= 0 => Some(i128::from(*value)),
        _ => None,
    }
}

/// When `term` is a base plus a constant in `domain`, or a conversion that
/// keeps its operand's value: the base's domain, the base, the constant,
/// and whether only a non-negative base keeps its value.
fn link_parts(
    domain: Domain,
    term: &Bitvector32Term,
) -> Option<(Domain, &Bitvector32Term, i128, bool)> {
    use Bitvector32Term as T;
    match (domain, term) {
        (Domain::Int32, T::Add(left, right))
        | (Domain::Int64, T::Int64Add(left, right))
        | (Domain::UInt64, T::UInt64Add(left, right)) => {
            if let Some(k) = constant(domain, right) {
                Some((domain, left, k, false))
            } else {
                constant(domain, left).map(|k| (domain, right.as_ref(), k, false))
            }
        }
        (Domain::Int32, T::Subtract(left, right))
        | (Domain::Int64, T::Int64Subtract(left, right))
        | (Domain::UInt64, T::UInt64Subtract(left, right)) => {
            constant(domain, right).map(|k| (domain, left.as_ref(), -k, false))
        }
        // Sign extension keeps every value.
        (Domain::Int64, T::Int64From32(inner)) => Some((Domain::Int32, inner, 0, false)),
        // Reinterpreting as unsigned keeps a non-negative value.
        (Domain::UInt64, T::UInt64From32(inner)) => Some((Domain::Int32, inner, 0, true)),
        (Domain::UInt64, T::UInt64FromInt64(inner)) => Some((Domain::Int64, inner, 0, true)),
        _ => None,
    }
}

/// The orders a condition with `value` states, as
/// `(domain, lower, upper, strict)` for `lower < upper` or `lower <= upper`;
/// a true equality is two. Empty for a fact difference logic does not
/// express.
fn condition_orders(
    condition: &ConditionTerm,
    value: bool,
) -> Vec<(Domain, Bitvector32Term, Bitvector32Term, bool)> {
    use ConditionTerm as C;
    let (domain, left, right, strict) = match condition {
        C::Bitvector32SignedLessThan(a, b) => (Domain::Int32, a, b, true),
        C::Bitvector32SignedLessEqual(a, b) => (Domain::Int32, a, b, false),
        C::Bitvector32SignedGreaterThan(a, b) => (Domain::Int32, b, a, true),
        C::Bitvector32SignedGreaterEqual(a, b) => (Domain::Int32, b, a, false),
        C::Bitvector64SignedLessThan(a, b) => (Domain::Int64, a, b, true),
        C::Bitvector64SignedLessEqual(a, b) => (Domain::Int64, a, b, false),
        C::Bitvector64SignedGreaterThan(a, b) => (Domain::Int64, b, a, true),
        C::Bitvector64SignedGreaterEqual(a, b) => (Domain::Int64, b, a, false),
        C::Bitvector64UnsignedLessThan(a, b) => (Domain::UInt64, a, b, true),
        C::Bitvector64UnsignedLessEqual(a, b) => (Domain::UInt64, a, b, false),
        C::Bitvector64UnsignedGreaterThan(a, b) => (Domain::UInt64, b, a, true),
        C::Bitvector64UnsignedGreaterEqual(a, b) => (Domain::UInt64, b, a, false),
        C::Bitvector32Equal(a, b) | C::Bitvector64Equal(a, b) if value => {
            let domains: &[Domain] = if matches!(condition, C::Bitvector32Equal(..)) {
                &[Domain::Int32]
            } else {
                &[Domain::Int64, Domain::UInt64]
            };
            let (a, b) = (a.as_ref(), b.as_ref());
            return domains
                .iter()
                .flat_map(|domain| {
                    [
                        (*domain, a.clone(), b.clone(), false),
                        (*domain, b.clone(), a.clone(), false),
                    ]
                })
                .collect();
        }
        _ => return Vec::new(),
    };
    let (left, right) = (left.as_ref().clone(), right.as_ref().clone());
    if value {
        vec![(domain, left, right, strict)]
    } else {
        // not (l < r) is r <= l; not (l <= r) is r < l.
        vec![(domain, right, left, !strict)]
    }
}

#[cfg(test)]
#[path = "difference_graph/tests.rs"]
pub(crate) mod tests;
