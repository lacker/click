//! A small list experiment built on the cons/nil kernel.
//!
//! This proves concrete finite facts about `reverse` with `Proof::Steps`.
//! General reverse theorems should use the kernel's list proposition and
//! induction rule rather than a userspace list recognizer.

use crate::{
    Lambda, ListCase, Proof, Prop, Step, Symbol, Term, Theorem, and, check, computes_to,
    computes_to_list, exists, forall, implies, is_list, normal_form, reverse_accumulates, step,
};

pub const UNIT: Symbol = 3;

const LIST: Symbol = 1_000;
const CELL: Symbol = 1_001;
const SELF: Symbol = 1_002;
const ACC: Symbol = 1_003;
const FIXED_POINT_FUNCTION: Symbol = 1_004;
const FIXED_POINT_SELF: Symbol = 1_005;
const FIXED_POINT_VALUE: Symbol = 1_006;
const LOOP_ARGUMENT: Symbol = 1_007;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvaluationProofError {
    StepLimitExceeded { limit: usize },
    UnexpectedNormalForm { expected: Term, actual: Term },
}

pub fn quote(symbol: Symbol) -> Term {
    Term::Quote(symbol)
}

pub fn var(symbol: Symbol) -> Term {
    Term::Var(symbol)
}

pub fn lambda(parameter: Symbol, body: Term) -> Term {
    Term::Lambda(Lambda {
        parameter,
        body: Box::new(body),
    })
}

pub fn apply(function: Term, argument: Term) -> Term {
    Term::Apply {
        function: Box::new(function),
        argument: Box::new(argument),
    }
}

pub fn nil() -> Term {
    Term::Nil
}

pub fn cons(head: Term, tail: Term) -> Term {
    Term::Cons {
        head: Box::new(head),
        tail: Box::new(tail),
    }
}

pub fn head(term: Term) -> Term {
    Term::Head(Box::new(term))
}

pub fn tail(term: Term) -> Term {
    Term::Tail(Box::new(term))
}

pub fn list_case(list: Term, nil: Term, cons: Symbol, cons_case: Term) -> Term {
    Term::ListCase(ListCase {
        list: Box::new(list),
        nil: Box::new(nil),
        cons,
        cons_case: Box::new(cons_case),
    })
}

pub fn unit() -> Term {
    quote(UNIT)
}

pub fn error(symbol: Symbol) -> Term {
    Term::Error(Box::new(quote(symbol)))
}

pub fn singleton(value: Term) -> Term {
    cons(value, nil())
}

pub fn pair(first: Term, second: Term) -> Term {
    cons(first, singleton(second))
}

pub fn triple(first: Term, second: Term, third: Term) -> Term {
    cons(first, pair(second, third))
}

/// The call-by-value fixed-point combinator.
///
/// The ordinary Y combinator unfolds too eagerly under this evaluator; this Z
/// combinator delays the recursive self-reference under an extra lambda.
pub fn z_combinator() -> Term {
    lambda(
        FIXED_POINT_FUNCTION,
        apply(fixed_point_half(), fixed_point_half()),
    )
}

fn fixed_point_half() -> Term {
    lambda(
        FIXED_POINT_SELF,
        apply(
            var(FIXED_POINT_FUNCTION),
            lambda(
                FIXED_POINT_VALUE,
                apply(
                    apply(var(FIXED_POINT_SELF), var(FIXED_POINT_SELF)),
                    var(FIXED_POINT_VALUE),
                ),
            ),
        ),
    )
}

pub fn reverse_acc() -> Term {
    apply(z_combinator(), reverse_acc_body())
}

fn reverse_acc_body() -> Term {
    lambda(
        SELF,
        lambda(
            LIST,
            lambda(
                ACC,
                list_case(
                    var(LIST),
                    var(ACC),
                    CELL,
                    apply(
                        apply(var(SELF), tail(var(CELL))),
                        cons(head(var(CELL)), var(ACC)),
                    ),
                ),
            ),
        ),
    )
}

pub fn reverse() -> Term {
    lambda(LIST, reverse_acc_call(var(LIST), nil()))
}

pub fn reverse_call(value: Term) -> Term {
    apply(reverse(), value)
}

pub fn reverse_acc_call(list: Term, acc: Term) -> Term {
    apply(apply(reverse_acc(), list), acc)
}

fn computes_to_reverse_acc(result: Symbol, term: Term, list: Term, acc: Term) -> Prop {
    exists(
        result,
        and(
            computes_to(term, var(result)),
            reverse_accumulates(list, acc, var(result)),
        ),
    )
}

/// If `list` and `acc` are lists, then `reverse_acc(list, acc)` computes to a list.
///
/// `result` names the existential result in `computes_to_list` and should be
/// distinct from `list` and `acc`.
pub fn reverse_acc_computes_to_list_theorem(list: Symbol, acc: Symbol, result: Symbol) -> Prop {
    forall(
        list,
        implies(
            is_list(var(list)),
            forall(
                acc,
                implies(
                    is_list(var(acc)),
                    computes_to_list(result, reverse_acc_call(var(list), var(acc))),
                ),
            ),
        ),
    )
}

/// If `list` is a list, then `reverse(list)` computes to a list.
///
/// `result` names the existential result in `computes_to_list` and should be
/// distinct from `list`.
pub fn reverse_computes_to_list_theorem(list: Symbol, result: Symbol) -> Prop {
    forall(
        list,
        implies(
            is_list(var(list)),
            computes_to_list(result, reverse_call(var(list))),
        ),
    )
}

/// If `list` and `acc` are lists, then `reverse_acc(list, acc)` computes to a
/// result satisfying the accumulator-reversal relation.
///
/// `result` names the existential result and should be distinct from `list`
/// and `acc`.
pub fn reverse_acc_correctness_theorem(list: Symbol, acc: Symbol, result: Symbol) -> Prop {
    forall(
        list,
        implies(
            is_list(var(list)),
            forall(
                acc,
                implies(
                    is_list(var(acc)),
                    computes_to_reverse_acc(
                        result,
                        reverse_acc_call(var(list), var(acc)),
                        var(list),
                        var(acc),
                    ),
                ),
            ),
        ),
    )
}

/// If `list` is a list, then `reverse(list)` computes to a result satisfying
/// the accumulator-reversal relation with a nil initial accumulator.
///
/// `result` names the existential result and should be distinct from `list`.
pub fn reverse_correctness_theorem(list: Symbol, result: Symbol) -> Prop {
    forall(
        list,
        implies(
            is_list(var(list)),
            computes_to_reverse_acc(result, reverse_call(var(list)), var(list), nil()),
        ),
    )
}

/// A function whose result is the denotational divergence marker.
pub fn loop_forever() -> Term {
    lambda(LOOP_ARGUMENT, Term::Diverge)
}

pub fn loop_forever_call() -> Term {
    apply(loop_forever(), unit())
}

/// Build the concrete evaluator path for a term, stopping at a normal form.
pub fn evaluation_chain(term: Term, limit: usize) -> Result<Vec<Term>, EvaluationProofError> {
    let mut term = term;
    let mut chain = vec![term.clone()];

    for _ in 0..limit {
        match step(&term) {
            Step::Reduced(next) => {
                chain.push(next.clone());
                term = next;
            }
            Step::Normal => return Ok(chain),
        }
    }

    Err(EvaluationProofError::StepLimitExceeded { limit })
}

/// A small tactic that turns bounded evaluation into a `Proof::Steps` object.
pub fn proof_by_evaluation(
    term: Term,
    expected: Term,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let chain = evaluation_chain(term, limit)?;
    let actual = chain
        .last()
        .cloned()
        .expect("evaluation chains are nonempty");

    if actual != expected {
        return Err(EvaluationProofError::UnexpectedNormalForm { expected, actual });
    }

    Ok(Proof::Steps(chain))
}

pub fn check_evaluates_to(term: Term, value: Term, proof: &Proof) -> bool {
    check(proof, &computes_to(term, value))
}

fn assume(assumption: Symbol) -> Proof {
    Proof::Assume(assumption)
}

fn forall_intro(variable: Symbol, proof: Proof) -> Proof {
    Proof::ForAllIntro {
        variable,
        proof: Box::new(proof),
    }
}

fn implies_intro(assumption: Symbol, premise: Prop, proof: Proof) -> Proof {
    Proof::ImpliesIntro {
        assumption,
        premise,
        proof: Box::new(proof),
    }
}

fn forall_elim(forall: Proof, argument: Term) -> Proof {
    Proof::ForAllElim {
        forall: Box::new(forall),
        argument,
    }
}

fn implies_elim(implication: Proof, premise: Proof) -> Proof {
    Proof::ImpliesElim {
        implication: Box::new(implication),
        premise: Box::new(premise),
    }
}

fn exists_intro(variable: Symbol, body: Prop, witness: Term, proof: Proof) -> Proof {
    Proof::ExistsIntro {
        variable,
        body,
        witness,
        proof: Box::new(proof),
    }
}

fn exists_elim(existential: Proof, witness: Symbol, assumption: Symbol, proof: Proof) -> Proof {
    Proof::ExistsElim {
        existential: Box::new(existential),
        witness,
        assumption,
        proof: Box::new(proof),
    }
}

fn and_intro(left: Proof, right: Proof) -> Proof {
    Proof::AndIntro(Box::new(left), Box::new(right))
}

fn and_elim_left(proof: Proof) -> Proof {
    Proof::AndElimLeft(Box::new(proof))
}

fn and_elim_right(proof: Proof) -> Proof {
    Proof::AndElimRight(Box::new(proof))
}

fn symm(proof: Proof) -> Proof {
    Proof::Symm(Box::new(proof))
}

fn rewrite(equality: Proof, proof: Proof, variable: Symbol, template: Prop) -> Proof {
    Proof::Rewrite {
        equality: Box::new(equality),
        proof: Box::new(proof),
        variable,
        template,
    }
}

fn checked_theorem(proof: Proof, prop: Prop) -> Theorem {
    Theorem::from_proof(proof, prop).expect("constructed theorem proof should check")
}

/// Proves `reverse_acc_computes_to_list_theorem(list, acc, result)`.
///
/// `list`, `acc`, and `result` should be distinct theorem variables. Internal
/// proof symbols are generated fresh from those inputs.
pub fn reverse_acc_computes_to_list_proof(list: Symbol, acc: Symbol, result: Symbol) -> Proof {
    let mut used = reserved_proof_symbols();
    let symbols = fresh_reverse_acc_proof_symbols(list, acc, result, &mut used);

    reverse_acc_computes_to_list_proof_with_symbols(symbols)
}

pub fn reverse_acc_computes_to_list(list: Symbol, acc: Symbol, result: Symbol) -> Theorem {
    checked_theorem(
        reverse_acc_computes_to_list_proof(list, acc, result),
        reverse_acc_computes_to_list_theorem(list, acc, result),
    )
}

/// Proves `reverse_computes_to_list_theorem(input, result)`.
///
/// `input` and `result` should be distinct theorem variables. Internal proof
/// symbols are generated fresh from those inputs.
pub fn reverse_computes_to_list_proof(input: Symbol, result: Symbol) -> Proof {
    let mut used = reserved_proof_symbols();
    add_used_symbol(&mut used, input);
    add_used_symbol(&mut used, result);

    let input_is_list_assumption = next_fresh_symbol(&mut used);
    let accumulator_theorem_list = next_fresh_symbol(&mut used);
    let accumulator = next_fresh_symbol(&mut used);
    let accumulator_symbols =
        fresh_reverse_acc_proof_symbols(accumulator_theorem_list, accumulator, result, &mut used);
    let rewrite_target = next_fresh_symbol(&mut used);

    reverse_computes_to_list_proof_with_symbols(ReverseProofSymbols {
        input,
        result,
        input_is_list_assumption,
        accumulator_symbols,
        rewrite_target,
    })
}

pub fn reverse_computes_to_list(input: Symbol, result: Symbol) -> Theorem {
    checked_theorem(
        reverse_computes_to_list_proof(input, result),
        reverse_computes_to_list_theorem(input, result),
    )
}

/// Proves `reverse_acc_correctness_theorem(list, acc, result)`.
///
/// `list`, `acc`, and `result` should be distinct theorem variables. Internal
/// proof symbols are generated fresh from those inputs.
pub fn reverse_acc_correctness_proof(list: Symbol, acc: Symbol, result: Symbol) -> Proof {
    let mut used = reserved_proof_symbols();
    let symbols = fresh_reverse_acc_correctness_proof_symbols(list, acc, result, &mut used);

    reverse_acc_correctness_proof_with_symbols(symbols)
}

pub fn reverse_acc_correctness(list: Symbol, acc: Symbol, result: Symbol) -> Theorem {
    checked_theorem(
        reverse_acc_correctness_proof(list, acc, result),
        reverse_acc_correctness_theorem(list, acc, result),
    )
}

/// Proves `reverse_correctness_theorem(input, result)`.
///
/// `input` and `result` should be distinct theorem variables. Internal proof
/// symbols are generated fresh from those inputs.
pub fn reverse_correctness_proof(input: Symbol, result: Symbol) -> Proof {
    let mut used = reserved_proof_symbols();
    add_used_symbol(&mut used, input);
    add_used_symbol(&mut used, result);

    let input_is_list_assumption = next_fresh_symbol(&mut used);
    let accumulator_theorem_list = next_fresh_symbol(&mut used);
    let accumulator = next_fresh_symbol(&mut used);
    let accumulator_symbols = fresh_reverse_acc_correctness_proof_symbols(
        accumulator_theorem_list,
        accumulator,
        result,
        &mut used,
    );
    let rewrite_target = next_fresh_symbol(&mut used);

    reverse_correctness_proof_with_symbols(ReverseCorrectnessProofSymbols {
        input,
        result,
        input_is_list_assumption,
        accumulator_symbols,
        rewrite_target,
    })
}

pub fn reverse_correctness(input: Symbol, result: Symbol) -> Theorem {
    checked_theorem(
        reverse_correctness_proof(input, result),
        reverse_correctness_theorem(input, result),
    )
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReverseAccProofSymbols {
    list: Symbol,
    acc: Symbol,
    result: Symbol,
    acc_is_list_assumption: Symbol,
    head: Symbol,
    tail: Symbol,
    head_is_value_assumption: Symbol,
    tail_is_list_assumption: Symbol,
    induction_hypothesis_assumption: Symbol,
    rewrite_target: Symbol,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReverseAccCorrectnessProofSymbols {
    list: Symbol,
    acc: Symbol,
    result: Symbol,
    acc_is_list_assumption: Symbol,
    head: Symbol,
    tail: Symbol,
    head_is_value_assumption: Symbol,
    tail_is_list_assumption: Symbol,
    induction_hypothesis_assumption: Symbol,
    recursive_result: Symbol,
    recursive_result_assumption: Symbol,
    rewrite_target: Symbol,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReverseProofSymbols {
    input: Symbol,
    result: Symbol,
    input_is_list_assumption: Symbol,
    accumulator_symbols: ReverseAccProofSymbols,
    rewrite_target: Symbol,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ReverseCorrectnessProofSymbols {
    input: Symbol,
    result: Symbol,
    input_is_list_assumption: Symbol,
    accumulator_symbols: ReverseAccCorrectnessProofSymbols,
    rewrite_target: Symbol,
}

fn reserved_proof_symbols() -> Vec<Symbol> {
    vec![
        UNIT,
        LIST,
        CELL,
        SELF,
        ACC,
        FIXED_POINT_FUNCTION,
        FIXED_POINT_SELF,
        FIXED_POINT_VALUE,
        LOOP_ARGUMENT,
    ]
}

fn fresh_reverse_acc_proof_symbols(
    list: Symbol,
    acc: Symbol,
    result: Symbol,
    used: &mut Vec<Symbol>,
) -> ReverseAccProofSymbols {
    add_used_symbol(used, list);
    add_used_symbol(used, acc);
    add_used_symbol(used, result);

    ReverseAccProofSymbols {
        list,
        acc,
        result,
        acc_is_list_assumption: next_fresh_symbol(used),
        head: next_fresh_symbol(used),
        tail: next_fresh_symbol(used),
        head_is_value_assumption: next_fresh_symbol(used),
        tail_is_list_assumption: next_fresh_symbol(used),
        induction_hypothesis_assumption: next_fresh_symbol(used),
        rewrite_target: next_fresh_symbol(used),
    }
}

fn fresh_reverse_acc_correctness_proof_symbols(
    list: Symbol,
    acc: Symbol,
    result: Symbol,
    used: &mut Vec<Symbol>,
) -> ReverseAccCorrectnessProofSymbols {
    add_used_symbol(used, list);
    add_used_symbol(used, acc);
    add_used_symbol(used, result);

    ReverseAccCorrectnessProofSymbols {
        list,
        acc,
        result,
        acc_is_list_assumption: next_fresh_symbol(used),
        head: next_fresh_symbol(used),
        tail: next_fresh_symbol(used),
        head_is_value_assumption: next_fresh_symbol(used),
        tail_is_list_assumption: next_fresh_symbol(used),
        induction_hypothesis_assumption: next_fresh_symbol(used),
        recursive_result: next_fresh_symbol(used),
        recursive_result_assumption: next_fresh_symbol(used),
        rewrite_target: next_fresh_symbol(used),
    }
}

fn add_used_symbol(used: &mut Vec<Symbol>, symbol: Symbol) {
    if !used.contains(&symbol) {
        used.push(symbol);
    }
}

fn next_fresh_symbol(used: &mut Vec<Symbol>) -> Symbol {
    let mut symbol = 0;
    while used.contains(&symbol) {
        symbol += 1;
    }

    used.push(symbol);
    symbol
}

fn reverse_acc_nil_base_proof(acc: Symbol, result: Symbol, assumption: Symbol) -> Proof {
    let term = reverse_acc_call(nil(), var(acc));
    let result_body = and(computes_to(term.clone(), var(result)), is_list(var(result)));
    let evaluation = proof_by_evaluation(term, var(acc), 128).expect("base case should reduce");

    Proof::ForAllIntro {
        variable: acc,
        proof: Box::new(Proof::ImpliesIntro {
            assumption,
            premise: is_list(var(acc)),
            proof: Box::new(Proof::ExistsIntro {
                variable: result,
                body: result_body,
                witness: var(acc),
                proof: Box::new(Proof::AndIntro(
                    Box::new(evaluation),
                    Box::new(Proof::Assume(assumption)),
                )),
            }),
        }),
    }
}

fn reverse_acc_cons_unfolding_proof(head: Symbol, tail: Symbol, acc: Symbol) -> Proof {
    let start = reverse_acc_call(cons(var(head), var(tail)), var(acc));
    let recursive = reverse_acc_call(var(tail), cons(var(head), var(acc)));
    let normal = normal_form(&recursive);
    let start_to_normal =
        proof_by_evaluation(start, normal.clone(), 128).expect("start should unfold");
    let recursive_to_normal =
        proof_by_evaluation(recursive, normal, 128).expect("recursive call should unfold");

    Proof::Trans(
        Box::new(start_to_normal),
        Box::new(Proof::Symm(Box::new(recursive_to_normal))),
    )
}

fn reverse_acc_cons_step_proof(symbols: ReverseAccProofSymbols) -> Proof {
    let recursive_acc = cons(var(symbols.head), var(symbols.acc));
    let accumulator_is_list = Proof::ListCons {
        head: var(symbols.head),
        tail: var(symbols.acc),
        head_is_value: Box::new(Proof::Assume(symbols.head_is_value_assumption)),
        tail_is_list: Box::new(Proof::Assume(symbols.acc_is_list_assumption)),
    };
    let induction_hypothesis = Proof::ImpliesElim {
        implication: Box::new(Proof::ForAllElim {
            forall: Box::new(Proof::Assume(symbols.induction_hypothesis_assumption)),
            argument: recursive_acc,
        }),
        premise: Box::new(accumulator_is_list),
    };
    let rewrite = Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(reverse_acc_cons_unfolding_proof(
            symbols.head,
            symbols.tail,
            symbols.acc,
        )))),
        proof: Box::new(induction_hypothesis),
        variable: symbols.rewrite_target,
        template: computes_to_list(symbols.result, var(symbols.rewrite_target)),
    };

    Proof::ForAllIntro {
        variable: symbols.acc,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: symbols.acc_is_list_assumption,
            premise: is_list(var(symbols.acc)),
            proof: Box::new(rewrite),
        }),
    }
}

fn reverse_acc_computes_to_list_proof_with_symbols(symbols: ReverseAccProofSymbols) -> Proof {
    let property = forall(
        symbols.acc,
        implies(
            is_list(var(symbols.acc)),
            computes_to_list(
                symbols.result,
                reverse_acc_call(var(symbols.list), var(symbols.acc)),
            ),
        ),
    );

    Proof::ListInduction {
        variable: symbols.list,
        property,
        base: Box::new(reverse_acc_nil_base_proof(
            symbols.acc,
            symbols.result,
            symbols.acc_is_list_assumption,
        )),
        head: symbols.head,
        tail: symbols.tail,
        head_is_value_assumption: symbols.head_is_value_assumption,
        tail_is_list_assumption: symbols.tail_is_list_assumption,
        induction_hypothesis_assumption: symbols.induction_hypothesis_assumption,
        step: Box::new(reverse_acc_cons_step_proof(symbols)),
    }
}

fn reverse_computes_to_list_proof_with_symbols(symbols: ReverseProofSymbols) -> Proof {
    let accumulator_theorem =
        reverse_acc_computes_to_list_proof_with_symbols(symbols.accumulator_symbols);
    let accumulator_result = Proof::ImpliesElim {
        implication: Box::new(Proof::ForAllElim {
            forall: Box::new(Proof::ImpliesElim {
                implication: Box::new(Proof::ForAllElim {
                    forall: Box::new(accumulator_theorem),
                    argument: var(symbols.input),
                }),
                premise: Box::new(Proof::Assume(symbols.input_is_list_assumption)),
            }),
            argument: nil(),
        }),
        premise: Box::new(Proof::ListNil),
    };
    let rewrite = Proof::Rewrite {
        equality: Box::new(Proof::Symm(Box::new(Proof::Step(reverse_call(var(
            symbols.input,
        )))))),
        proof: Box::new(accumulator_result),
        variable: symbols.rewrite_target,
        template: computes_to_list(symbols.result, var(symbols.rewrite_target)),
    };

    Proof::ForAllIntro {
        variable: symbols.input,
        proof: Box::new(Proof::ImpliesIntro {
            assumption: symbols.input_is_list_assumption,
            premise: is_list(var(symbols.input)),
            proof: Box::new(rewrite),
        }),
    }
}

fn reverse_acc_correctness_nil_base_proof(
    acc: Symbol,
    result: Symbol,
    assumption: Symbol,
) -> Proof {
    let term = reverse_acc_call(nil(), var(acc));
    let result_body = and(
        computes_to(term.clone(), var(result)),
        reverse_accumulates(nil(), var(acc), var(result)),
    );
    let evaluation = proof_by_evaluation(term, var(acc), 128).expect("base case should reduce");
    let relation = Proof::ReverseAccNil { acc: var(acc) };

    forall_intro(
        acc,
        implies_intro(
            assumption,
            is_list(var(acc)),
            exists_intro(
                result,
                result_body,
                var(acc),
                and_intro(evaluation, relation),
            ),
        ),
    )
}

fn reverse_acc_correctness_cons_step_proof(symbols: ReverseAccCorrectnessProofSymbols) -> Proof {
    let recursive_acc = cons(var(symbols.head), var(symbols.acc));
    let start = reverse_acc_call(cons(var(symbols.head), var(symbols.tail)), var(symbols.acc));
    let accumulator_is_list = Proof::ListCons {
        head: var(symbols.head),
        tail: var(symbols.acc),
        head_is_value: Box::new(assume(symbols.head_is_value_assumption)),
        tail_is_list: Box::new(assume(symbols.acc_is_list_assumption)),
    };
    let induction_hypothesis = implies_elim(
        forall_elim(
            assume(symbols.induction_hypothesis_assumption),
            recursive_acc.clone(),
        ),
        accumulator_is_list,
    );
    let recursive_fact = assume(symbols.recursive_result_assumption);
    let recursive_computes = and_elim_left(recursive_fact.clone());
    let recursive_relation = and_elim_right(recursive_fact);
    let start_computes = rewrite(
        symm(reverse_acc_cons_unfolding_proof(
            symbols.head,
            symbols.tail,
            symbols.acc,
        )),
        recursive_computes,
        symbols.rewrite_target,
        computes_to(var(symbols.rewrite_target), var(symbols.recursive_result)),
    );
    let relation = Proof::ReverseAccCons {
        head: var(symbols.head),
        tail: var(symbols.tail),
        acc: var(symbols.acc),
        result: var(symbols.recursive_result),
        head_is_value: Box::new(assume(symbols.head_is_value_assumption)),
        tail_reverse_acc: Box::new(recursive_relation),
    };
    let result_body = and(
        computes_to(start.clone(), var(symbols.result)),
        reverse_accumulates(
            cons(var(symbols.head), var(symbols.tail)),
            var(symbols.acc),
            var(symbols.result),
        ),
    );
    let result_proof = exists_intro(
        symbols.result,
        result_body,
        var(symbols.recursive_result),
        and_intro(start_computes, relation),
    );

    forall_intro(
        symbols.acc,
        implies_intro(
            symbols.acc_is_list_assumption,
            is_list(var(symbols.acc)),
            exists_elim(
                induction_hypothesis,
                symbols.recursive_result,
                symbols.recursive_result_assumption,
                result_proof,
            ),
        ),
    )
}

fn reverse_acc_correctness_proof_with_symbols(symbols: ReverseAccCorrectnessProofSymbols) -> Proof {
    let property = forall(
        symbols.acc,
        implies(
            is_list(var(symbols.acc)),
            computes_to_reverse_acc(
                symbols.result,
                reverse_acc_call(var(symbols.list), var(symbols.acc)),
                var(symbols.list),
                var(symbols.acc),
            ),
        ),
    );

    Proof::ListInduction {
        variable: symbols.list,
        property,
        base: Box::new(reverse_acc_correctness_nil_base_proof(
            symbols.acc,
            symbols.result,
            symbols.acc_is_list_assumption,
        )),
        head: symbols.head,
        tail: symbols.tail,
        head_is_value_assumption: symbols.head_is_value_assumption,
        tail_is_list_assumption: symbols.tail_is_list_assumption,
        induction_hypothesis_assumption: symbols.induction_hypothesis_assumption,
        step: Box::new(reverse_acc_correctness_cons_step_proof(symbols)),
    }
}

fn reverse_correctness_proof_with_symbols(symbols: ReverseCorrectnessProofSymbols) -> Proof {
    let accumulator_theorem =
        reverse_acc_correctness_proof_with_symbols(symbols.accumulator_symbols);
    let accumulator_result = implies_elim(
        forall_elim(
            implies_elim(
                forall_elim(accumulator_theorem, var(symbols.input)),
                assume(symbols.input_is_list_assumption),
            ),
            nil(),
        ),
        Proof::ListNil,
    );
    let rewrite = rewrite(
        symm(Proof::Step(reverse_call(var(symbols.input)))),
        accumulator_result,
        symbols.rewrite_target,
        computes_to_reverse_acc(
            symbols.result,
            var(symbols.rewrite_target),
            var(symbols.input),
            nil(),
        ),
    );

    forall_intro(
        symbols.input,
        implies_intro(
            symbols.input_is_list_assumption,
            is_list(var(symbols.input)),
            rewrite,
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Proof, check, diverges, exists};

    const A: Symbol = 100;
    const B: Symbol = 101;
    const NOT_A_LIST: Symbol = 102;
    const X: Symbol = 200;
    const ACCUMULATOR: Symbol = 201;
    const RESULT: Symbol = 202;
    const HEAD: Symbol = 203;
    const TAIL: Symbol = 204;
    const ACCUMULATOR_IS_LIST: Symbol = 205;

    fn prove_evaluation(term: Term, expected: Term) -> Proof {
        proof_by_evaluation(term, expected, 512).expect("example should evaluate")
    }

    fn assert_evaluates(term: Term, expected: Term) {
        let proof = prove_evaluation(term.clone(), expected.clone());
        assert!(check_evaluates_to(term, expected, &proof));
    }

    #[test]
    fn reverse_acc_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    forall(
                        ACCUMULATOR,
                        implies(
                            is_list(var(ACCUMULATOR)),
                            exists(
                                RESULT,
                                and(
                                    computes_to(
                                        reverse_acc_call(var(X), var(ACCUMULATOR)),
                                        var(RESULT),
                                    ),
                                    is_list(var(RESULT)),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_computes_to_list_theorem_has_expected_shape() {
        assert_eq!(
            reverse_computes_to_list_theorem(X, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    exists(
                        RESULT,
                        and(
                            computes_to(reverse_call(var(X)), var(RESULT)),
                            is_list(var(RESULT)),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_acc_correctness_theorem_has_expected_shape() {
        assert_eq!(
            reverse_acc_correctness_theorem(X, ACCUMULATOR, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    forall(
                        ACCUMULATOR,
                        implies(
                            is_list(var(ACCUMULATOR)),
                            exists(
                                RESULT,
                                and(
                                    computes_to(
                                        reverse_acc_call(var(X), var(ACCUMULATOR)),
                                        var(RESULT),
                                    ),
                                    reverse_accumulates(var(X), var(ACCUMULATOR), var(RESULT)),
                                ),
                            ),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_correctness_theorem_has_expected_shape() {
        assert_eq!(
            reverse_correctness_theorem(X, RESULT),
            forall(
                X,
                implies(
                    is_list(var(X)),
                    exists(
                        RESULT,
                        and(
                            computes_to(reverse_call(var(X)), var(RESULT)),
                            reverse_accumulates(var(X), nil(), var(RESULT)),
                        ),
                    ),
                ),
            )
        );
    }

    #[test]
    fn reverse_acc_nil_base_case_is_provable() {
        let theorem_base = forall(
            ACCUMULATOR,
            implies(
                is_list(var(ACCUMULATOR)),
                computes_to_list(RESULT, reverse_acc_call(nil(), var(ACCUMULATOR))),
            ),
        );

        assert!(check(
            &reverse_acc_nil_base_proof(ACCUMULATOR, RESULT, ACCUMULATOR_IS_LIST),
            &theorem_base,
        ));
    }

    #[test]
    fn reverse_acc_cons_case_symbolically_unfolds() {
        let start = reverse_acc_call(cons(var(HEAD), var(TAIL)), var(ACCUMULATOR));
        let recursive = reverse_acc_call(var(TAIL), cons(var(HEAD), var(ACCUMULATOR)));
        let proof = reverse_acc_cons_unfolding_proof(HEAD, TAIL, ACCUMULATOR);

        assert!(check(&proof, &computes_to(start, recursive)));
    }

    #[test]
    fn proves_reverse_acc_computes_to_list_for_all_lists() {
        let proof = reverse_acc_computes_to_list_proof(X, ACCUMULATOR, RESULT);

        assert!(check(
            &proof,
            &reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
        ));
    }

    #[test]
    fn proves_reverse_computes_to_list_for_all_lists() {
        let proof = reverse_computes_to_list_proof(X, RESULT);

        assert!(check(&proof, &reverse_computes_to_list_theorem(X, RESULT)));
    }

    #[test]
    fn proves_reverse_acc_correctness_for_all_lists() {
        let proof = reverse_acc_correctness_proof(X, ACCUMULATOR, RESULT);

        assert!(check(
            &proof,
            &reverse_acc_correctness_theorem(X, ACCUMULATOR, RESULT),
        ));
    }

    #[test]
    fn proves_reverse_correctness_for_all_lists() {
        let proof = reverse_correctness_proof(X, RESULT);

        assert!(check(&proof, &reverse_correctness_theorem(X, RESULT)));
    }

    #[test]
    fn checked_reverse_theorems_expose_theorem_values() {
        assert_eq!(
            reverse_acc_computes_to_list(X, ACCUMULATOR, RESULT).prop(),
            &reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
        );
        assert_eq!(
            reverse_computes_to_list(X, RESULT).prop(),
            &reverse_computes_to_list_theorem(X, RESULT),
        );
        assert_eq!(
            reverse_acc_correctness(X, ACCUMULATOR, RESULT).prop(),
            &reverse_acc_correctness_theorem(X, ACCUMULATOR, RESULT),
        );
        assert_eq!(
            reverse_correctness(X, RESULT).prop(),
            &reverse_correctness_theorem(X, RESULT),
        );
    }

    #[test]
    fn reverse_nil_terminates_without_error() {
        assert_evaluates(reverse_call(nil()), nil());
    }

    #[test]
    fn reverse_singleton_terminates_without_error() {
        let list = singleton(quote(A));

        assert_evaluates(reverse_call(list.clone()), list);
    }

    #[test]
    fn reverse_pair_terminates_without_error() {
        assert_evaluates(
            reverse_call(pair(quote(A), quote(B))),
            pair(quote(B), quote(A)),
        );
    }

    #[test]
    fn reverse_triple_terminates_without_error() {
        assert_evaluates(
            reverse_call(triple(quote(A), quote(B), quote(NOT_A_LIST))),
            triple(quote(NOT_A_LIST), quote(B), quote(A)),
        );
    }

    #[test]
    fn loop_forever_diverges() {
        let term = loop_forever_call();
        let proof = prove_evaluation(term.clone(), Term::Diverge);

        assert!(check(&proof, &diverges(term)));
    }

    #[test]
    fn reverse_non_list_input_reduces_to_error() {
        assert_evaluates(reverse_call(quote(NOT_A_LIST)), error(NOT_A_LIST));
    }

    #[test]
    fn reverse_malformed_tail_reduces_to_error() {
        assert_evaluates(
            reverse_call(cons(quote(A), quote(NOT_A_LIST))),
            error(NOT_A_LIST),
        );
    }

    #[test]
    fn evaluation_proof_rejects_wrong_expected_value() {
        assert_eq!(
            proof_by_evaluation(reverse_call(nil()), quote(NOT_A_LIST), 64),
            Err(EvaluationProofError::UnexpectedNormalForm {
                expected: quote(NOT_A_LIST),
                actual: nil(),
            })
        );
    }
}
