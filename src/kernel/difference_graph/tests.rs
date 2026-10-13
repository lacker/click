use super::*;
use crate::kernel::{PureFactContext, Variable};

thread_local! {
    pub(super) static GRAPH_WORK: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn graph_work<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    GRAPH_WORK.with(|work| work.set(0));
    let result = operation();
    (result, GRAPH_WORK.with(std::cell::Cell::get))
}

fn variable(id: u64) -> Bitvector32Term {
    Bitvector32Term::Variable(Variable(91_000 + id))
}

fn constant(value: i32) -> Bitvector32Term {
    Bitvector32Term::Constant(value as u32)
}

fn plus(term: &Bitvector32Term, value: i32) -> Bitvector32Term {
    Bitvector32Term::Add(Box::new(term.clone()), Box::new(constant(value)))
}

fn lt(a: &Bitvector32Term, b: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a.clone(), b.clone())
}

fn le(a: &Bitvector32Term, b: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_equal(a.clone(), b.clone())
}

fn add_overflows(a: &Bitvector32Term, b: &Bitvector32Term) -> ConditionTerm {
    ConditionTerm::Bitvector32SignedAddOverflows(Box::new(a.clone()), Box::new(b.clone()))
}

fn graph(facts: &[(ConditionTerm, bool)]) -> DifferenceGraph {
    let mut graph = DifferenceGraph::new();
    for (condition, value) in facts {
        graph.assume_condition(condition, *value);
    }
    graph
}

#[test]
fn constant_bounds_decide_orders_and_overflow() {
    let i = variable(0);
    let graph = graph(&[(le(&constant(0), &i), true), (lt(&i, &constant(4)), true)]);
    assert_eq!(graph.decide(&lt(&i, &constant(4))), Some(true));
    assert_eq!(graph.decide(&lt(&i, &constant(0))), Some(false));
    assert_eq!(graph.decide(&lt(&i, &constant(3))), None);
    // `i + 1` cannot overflow for `0 <= i < 4`.
    assert_eq!(graph.decide(&add_overflows(&i, &constant(1))), Some(false));
    assert_eq!(graph.decide(&lt(&plus(&i, 1), &constant(5))), Some(true));
}

#[test]
fn relations_between_values_decide_through_paths() {
    let (index, n, length) = (variable(0), variable(1), variable(2));
    let graph = graph(&[(lt(&index, &n), true), (le(&n, &length), true)]);
    assert_eq!(graph.decide(&lt(&index, &length)), Some(true));
    assert_eq!(graph.decide(&le(&length, &index)), Some(false));
    assert_eq!(graph.decide(&lt(&n, &index)), Some(false));
    assert_eq!(graph.decide(&lt(&length, &n)), Some(false));
    assert_eq!(graph.decide(&lt(&n, &length)), None);
}

#[test]
fn a_false_fact_states_its_negation() {
    let (x, y) = (variable(0), variable(1));
    let graph = graph(&[(lt(&x, &y), false)]);
    assert_eq!(graph.decide(&le(&y, &x)), Some(true));
}

#[test]
fn a_sum_is_linked_only_when_it_cannot_wrap() {
    let x = variable(0);
    let max = constant(i32::MAX);
    // Unbounded `x`: `x + 1` may wrap, so it says nothing about `x`.
    let unbounded = graph(&[(lt(&plus(&x, 1), &constant(10)), true)]);
    assert_eq!(unbounded.decide(&lt(&x, &constant(9))), None);
    assert_eq!(unbounded.decide(&add_overflows(&x, &constant(1))), None);
    // Bounded below `INT_MAX`: the sum is exact, and its bound reaches `x`.
    let bounded = graph(&[
        (lt(&x, &max), true),
        (lt(&plus(&x, 1), &constant(10)), true),
    ]);
    assert_eq!(bounded.decide(&lt(&x, &constant(9))), Some(true));
    // A bound that arrives after the sum still links it.
    let late = graph(&[
        (lt(&plus(&x, 1), &constant(10)), true),
        (lt(&x, &max), true),
    ]);
    assert_eq!(late.decide(&lt(&x, &constant(9))), Some(true));
}

#[test]
fn overflow_is_decided_at_the_edges_of_the_range() {
    let x = variable(0);
    let near_max = graph(&[(le(&constant(i32::MAX - 1), &x), true)]);
    assert_eq!(
        near_max.decide(&add_overflows(&x, &constant(2))),
        Some(true)
    );
    assert_eq!(near_max.decide(&add_overflows(&x, &constant(1))), None);
    let below = graph(&[(le(&x, &constant(i32::MAX - 1)), true)]);
    assert_eq!(below.decide(&add_overflows(&x, &constant(1))), Some(false));
}

#[test]
fn unsigned_conversion_keeps_a_nonnegative_value() {
    let i = variable(0);
    let wide = Bitvector32Term::UInt64From32(Box::new(i.clone()));
    let length = variable(1);
    let below =
        ConditionTerm::Bitvector64UnsignedLessThan(Box::new(wide), Box::new(length.clone()));
    let graph = graph(&[(le(&constant(0), &i), true), (below, true)]);
    let length_positive = ConditionTerm::Bitvector64UnsignedLessThan(
        Box::new(Bitvector32Term::UInt64Constant(0)),
        Box::new(length),
    );
    assert_eq!(graph.decide(&length_positive), Some(true));
}

#[test]
fn contradictions_are_detected_and_decide_nothing() {
    let (x, y) = (variable(0), variable(1));
    let cycle = graph(&[(lt(&x, &y), true), (lt(&y, &x), true)]);
    assert!(cycle.is_contradictory());
    assert_eq!(cycle.decide(&lt(&x, &y)), None);
    let bounds = graph(&[(lt(&x, &constant(3)), true), (lt(&constant(5), &x), true)]);
    assert!(bounds.is_contradictory());
}

#[test]
fn a_clone_is_a_branch() {
    let (x, y) = (variable(0), variable(1));
    let trunk = graph(&[(lt(&x, &y), true)]);
    let mut branch = trunk.clone();
    branch.assume_condition(&lt(&y, &constant(0)), true);
    assert_eq!(branch.decide(&lt(&x, &constant(-1))), Some(true));
    assert_eq!(trunk.decide(&lt(&x, &constant(-1))), None);
}

/// Generated fact sets over three variables bounded to [-4, 4], two constant
/// offsets of them, and constants, against every model: whatever the graph
/// decides holds in every model of the facts, and an order between two pool
/// terms that every model agrees on is decided (difference logic is
/// complete for these facts). The general decision, where it also answers,
/// agrees.
#[test]
fn decisions_hold_in_every_model_and_are_complete() {
    let variables = (0..3).map(variable).collect::<Vec<_>>();
    let mut pool = variables.clone();
    pool.push(plus(&variables[0], 1));
    pool.push(plus(&variables[1], -2));
    pool.extend([-2, 0, 3].map(constant));
    let value = |term: &Bitvector32Term, model: &[i128]| -> i128 {
        match term {
            Bitvector32Term::Constant(value) => i128::from(*value as i32),
            Bitvector32Term::Add(base, offset) => {
                let base = variables.iter().position(|v| v == base.as_ref()).unwrap();
                let Bitvector32Term::Constant(offset) = offset.as_ref() else {
                    unreachable!()
                };
                model[base] + i128::from(*offset as i32)
            }
            _ => model[variables.iter().position(|v| v == term).unwrap()],
        }
    };
    let holds = |condition: &ConditionTerm, model: &[i128]| -> bool {
        // The constructors fold a comparison of two constants.
        if let ConditionTerm::Constant(value) = condition {
            return *value;
        }
        let [(_, ref lower, ref upper, strict)] = condition_orders(condition, true)[..] else {
            unreachable!("{condition:?}")
        };
        let (lower, upper) = (value(lower, model), value(upper, model));
        if strict {
            lower < upper
        } else {
            lower <= upper
        }
    };
    let models = (0..9i128.pow(3))
        .map(|index| {
            (0..3)
                .map(|place| (index / 9i128.pow(place)) % 9 - 4)
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = |bound: usize| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        (state % bound as u64) as usize
    };
    let (mut decided, mut compared) = (0, 0);
    for _ in 0..40 {
        let mut facts = variables
            .iter()
            .flat_map(|v| [(le(&constant(-4), v), true), (le(v, &constant(4)), true)])
            .collect::<Vec<_>>();
        for _ in 0..(1 + next(4)) {
            let (a, b) = (&pool[next(pool.len())], &pool[next(pool.len())]);
            let condition = if next(2) == 0 { lt(a, b) } else { le(a, b) };
            facts.push((condition, next(3) != 0));
        }
        let graph = graph(&facts);
        let mut context = PureFactContext::new();
        for (condition, value) in &facts {
            context = context.assume_condition(condition.clone(), *value);
        }
        let satisfying = models
            .iter()
            .filter(|model| {
                facts
                    .iter()
                    .all(|(fact, value)| holds(fact, model) == *value)
            })
            .collect::<Vec<_>>();
        if satisfying.is_empty() {
            continue;
        }
        assert!(
            !graph.is_contradictory(),
            "satisfiable facts reported contradictory: {facts:?}"
        );
        for a in &pool {
            for b in &pool {
                for query in [lt(a, b), le(a, b)] {
                    let truths = satisfying
                        .iter()
                        .map(|model| holds(&query, model))
                        .collect::<std::collections::BTreeSet<_>>();
                    let entailed = (truths.len() == 1).then(|| truths.contains(&true));
                    let answer = graph.decide(&query);
                    assert!(
                        answer.is_none() || answer == entailed,
                        "{query:?} decided {answer:?} but the models say {entailed:?} under {facts:?}"
                    );
                    assert_eq!(
                        answer, entailed,
                        "{query:?} is entailed but undecided under {facts:?}"
                    );
                    if let (Some(answer), Some(general)) = (answer, context.decide(&query)) {
                        assert_eq!(answer, general, "{query:?} under {facts:?}");
                        compared += 1;
                    }
                    decided += usize::from(answer.is_some());
                }
            }
        }
    }
    assert!(
        decided > 0 && compared > 0,
        "the generated cases should decide something"
    );
}

/// Inserting a fact and answering a question cost the same beside 16 to
/// 1,024 unrelated bounded values: a constant is not a node, so their
/// bounds never join the component the fact or question touches.
#[test]
fn work_is_independent_of_unrelated_bounded_values() {
    let (i, n) = (variable(0), variable(1));
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut graph = DifferenceGraph::new();
        for index in 0..size {
            let other = variable(10 + index);
            graph.assume_condition(&le(&constant(0), &other), true);
            graph.assume_condition(&lt(&other, &constant(4)), true);
        }
        graph.assume_condition(&le(&constant(0), &i), true);
        let (_, insert) = graph_work(|| graph.assume_condition(&lt(&i, &n), true));
        let (answer, query) = graph_work(|| graph.decide(&lt(&i, &constant(4))));
        assert_eq!(answer, None);
        let (answer, path) = graph_work(|| graph.decide(&le(&i, &n)));
        assert_eq!(answer, Some(true));
        samples.push((insert, query, path));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "graph work should not grow with unrelated values: {samples:?}"
    );
    eprintln!(
        "difference graph (insert, bound query, path query) work at 16/64/256/1024: {samples:?}"
    );
}
