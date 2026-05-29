//! List definitions and theorems for the standard prelude.

use crate::{
    Lambda, ListCase, Name, Proof, Prop, Step, Symbol, Term, Theory, alpha_eq_term, and,
    computes_to, computes_to_list, forall, implies, is_list,
};

use super::{
    REVERSE, REVERSE_ACC, REVERSE_ACC_COMPUTES_TO_LIST, REVERSE_COMPUTES_TO_LIST,
    source::{
        NameBinding, ParseError, ParsedModule, ParsedTheorem, ProofExpr, ProofScript, SymbolBinding,
    },
};

pub const UNIT: Symbol = Symbol(3);

const SOURCE: &str = include_str!("list.lisp");

const LIST: Symbol = Symbol(1_000);
const CELL: Symbol = Symbol(1_001);
const SELF: Symbol = Symbol(1_002);
const ACC: Symbol = Symbol(1_003);
const FIXED_POINT_FUNCTION: Symbol = Symbol(1_004);
const FIXED_POINT_SELF: Symbol = Symbol(1_005);
const FIXED_POINT_VALUE: Symbol = Symbol(1_006);
const LOOP_ARGUMENT: Symbol = Symbol(1_007);

const TERM_DEFINITIONS: &[NameBinding] = &[
    NameBinding {
        spelling: "reverse_acc",
        name: REVERSE_ACC,
    },
    NameBinding {
        spelling: "reverse",
        name: REVERSE,
    },
];

const THEOREM_DEFINITIONS: &[NameBinding] = &[
    NameBinding {
        spelling: "reverse_acc_computes_to_list",
        name: REVERSE_ACC_COMPUTES_TO_LIST,
    },
    NameBinding {
        spelling: "reverse_computes_to_list",
        name: REVERSE_COMPUTES_TO_LIST,
    },
];

const TERM_SYMBOLS: &[SymbolBinding] = &[
    SymbolBinding {
        spelling: "unit",
        symbol: UNIT,
    },
    SymbolBinding {
        spelling: "list",
        symbol: LIST,
    },
    SymbolBinding {
        spelling: "cell",
        symbol: CELL,
    },
    SymbolBinding {
        spelling: "self",
        symbol: SELF,
    },
    SymbolBinding {
        spelling: "acc",
        symbol: ACC,
    },
    SymbolBinding {
        spelling: "fixed_point_function",
        symbol: FIXED_POINT_FUNCTION,
    },
    SymbolBinding {
        spelling: "fixed_point_self",
        symbol: FIXED_POINT_SELF,
    },
    SymbolBinding {
        spelling: "fixed_point_value",
        symbol: FIXED_POINT_VALUE,
    },
    SymbolBinding {
        spelling: "loop_argument",
        symbol: LOOP_ARGUMENT,
    },
];

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

pub fn reverse_acc() -> Term {
    super::reverse_acc()
}

pub(super) fn module() -> Result<ParsedModule, ParseError> {
    super::source::parse_module(SOURCE, TERM_DEFINITIONS, THEOREM_DEFINITIONS, TERM_SYMBOLS)
}

pub(super) fn term_definitions() -> Result<Vec<(Name, Term)>, ParseError> {
    Ok(module()?.terms)
}

pub(super) fn theorem_definitions() -> Result<Vec<ParsedTheorem>, ParseError> {
    Ok(module()?.theorems)
}

pub fn reverse_acc_definition() -> Term {
    definition(REVERSE_ACC)
}

pub fn reverse() -> Term {
    super::reverse()
}

pub fn reverse_definition() -> Term {
    definition(REVERSE)
}

fn definition(name: Name) -> Term {
    term_definitions()
        .expect("prelude list source should parse")
        .into_iter()
        .find_map(|(definition_name, term)| (definition_name == name).then_some(term))
        .expect("prelude list source should define requested term")
}

pub fn reverse_acc_computes_to_list_source_theorem() -> Prop {
    theorem_definition(REVERSE_ACC_COMPUTES_TO_LIST).prop
}

pub fn reverse_computes_to_list_source_theorem() -> Prop {
    theorem_definition(REVERSE_COMPUTES_TO_LIST).prop
}

fn theorem_definition(name: Name) -> ParsedTheorem {
    theorem_definitions()
        .expect("prelude list source should parse theorem statements")
        .into_iter()
        .find(|theorem| theorem.name == name)
        .expect("prelude list source should define requested theorem")
}

#[cfg(test)]
fn theorem_symbol(name: Name, spelling: &str) -> Symbol {
    theorem_definition(name)
        .symbol(spelling)
        .expect("prelude list source should define requested theorem symbol once")
}

pub fn reverse_acc_computes_to_list_source_proof() -> Proof {
    source_proof(REVERSE_ACC_COMPUTES_TO_LIST)
}

pub fn reverse_computes_to_list_source_proof() -> Proof {
    source_proof(REVERSE_COMPUTES_TO_LIST)
}

#[cfg(test)]
pub(super) fn reverse_computes_to_list_source_result_symbol() -> Symbol {
    theorem_symbol(REVERSE_COMPUTES_TO_LIST, "result")
}

pub(super) fn proof_for_theorem(theorem: &ParsedTheorem, theory: &Theory) -> Option<Proof> {
    match &theorem.proof {
        ProofScript::Proof(proof) => proof_expr_to_proof(proof, theory),
    }
}

fn source_proof(name: Name) -> Proof {
    let module = module().expect("prelude list source should parse");
    let mut theory = super::term_theory();

    for theorem in module.theorems {
        let proof =
            proof_for_theorem(&theorem, &theory).expect("prelude list source should prove theorem");

        if theorem.name == name {
            return proof;
        }

        theory
            .define_theorem_from_proof(theorem.name, proof, theorem.prop)
            .expect("prelude list source theorem dependency should check");
    }

    panic!("prelude list source should define requested theorem proof");
}

fn proof_expr_to_proof(proof: &ProofExpr, theory: &Theory) -> Option<Proof> {
    match proof {
        ProofExpr::Known(name) => Some(Proof::Known(*name)),
        ProofExpr::Assume(symbol) => Some(Proof::Assume(*symbol)),
        ProofExpr::Symm(proof) => Some(Proof::Symm(Box::new(proof_expr_to_proof(proof, theory)?))),
        ProofExpr::Trans(first, second) => Some(Proof::Trans(
            Box::new(proof_expr_to_proof(first, theory)?),
            Box::new(proof_expr_to_proof(second, theory)?),
        )),
        ProofExpr::EvalTo {
            term,
            expected,
            limit,
        } => proof_by_reduction_in_theory(term.clone(), expected.clone(), theory, *limit).ok(),
        ProofExpr::EvalSame { left, right, limit } => {
            proof_by_same_normal_form_in_theory(left.clone(), right.clone(), theory, *limit).ok()
        }
        ProofExpr::Rewrite {
            equality,
            proof,
            variable,
            template,
        } => Some(Proof::Rewrite {
            equality: Box::new(proof_expr_to_proof(equality, theory)?),
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
            variable: *variable,
            template: template.clone(),
        }),
        ProofExpr::ListNil => Some(Proof::ListNil),
        ProofExpr::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => Some(Proof::ImpliesIntro {
            assumption: *assumption,
            premise: premise.clone(),
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::ImpliesElim {
            implication,
            premise,
        } => Some(Proof::ImpliesElim {
            implication: Box::new(proof_expr_to_proof(implication, theory)?),
            premise: Box::new(proof_expr_to_proof(premise, theory)?),
        }),
        ProofExpr::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => Some(Proof::ExistsIntro {
            variable: *variable,
            body: body.clone(),
            witness: witness.clone(),
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::AndIntro(left, right) => Some(Proof::AndIntro(
            Box::new(proof_expr_to_proof(left, theory)?),
            Box::new(proof_expr_to_proof(right, theory)?),
        )),
        ProofExpr::ListCons {
            head,
            tail,
            head_is_value,
            tail_is_list,
        } => Some(Proof::ListCons {
            head: head.clone(),
            tail: tail.clone(),
            head_is_value: Box::new(proof_expr_to_proof(head_is_value, theory)?),
            tail_is_list: Box::new(proof_expr_to_proof(tail_is_list, theory)?),
        }),
        ProofExpr::ListInduction {
            variable,
            property,
            base,
            head,
            tail,
            head_is_value_assumption,
            tail_is_list_assumption,
            induction_hypothesis_assumption,
            step,
        } => Some(Proof::ListInduction {
            variable: *variable,
            property: property.clone(),
            base: Box::new(proof_expr_to_proof(base, theory)?),
            head: *head,
            tail: *tail,
            head_is_value_assumption: *head_is_value_assumption,
            tail_is_list_assumption: *tail_is_list_assumption,
            induction_hypothesis_assumption: *induction_hypothesis_assumption,
            step: Box::new(proof_expr_to_proof(step, theory)?),
        }),
        ProofExpr::ForAllIntro { variable, proof } => Some(Proof::ForAllIntro {
            variable: *variable,
            proof: Box::new(proof_expr_to_proof(proof, theory)?),
        }),
        ProofExpr::ForAllElim { forall, argument } => Some(Proof::ForAllElim {
            forall: Box::new(proof_expr_to_proof(forall, theory)?),
            argument: argument.clone(),
        }),
    }
}

pub fn reverse_call(value: Term) -> Term {
    apply(reverse(), value)
}

pub fn reverse_acc_call(list: Term, acc: Term) -> Term {
    apply(apply(reverse_acc(), list), acc)
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

/// A function whose result is the denotational divergence marker.
pub fn loop_forever() -> Term {
    lambda(LOOP_ARGUMENT, Term::Diverge)
}

pub fn loop_forever_call() -> Term {
    apply(loop_forever(), unit())
}

/// Build the concrete evaluator path using the prelude definitions.
pub fn evaluation_chain(term: Term, limit: usize) -> Result<Vec<Term>, EvaluationProofError> {
    let theory = super::term_theory();
    evaluation_chain_in_theory(term, &theory, limit)
}

pub fn evaluation_chain_in_theory(
    term: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Vec<Term>, EvaluationProofError> {
    let mut term = term;
    let mut chain = vec![term.clone()];

    for _ in 0..limit {
        match theory.reduce(&term) {
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
///
/// This uses the prelude term theory. Use `proof_by_evaluation_in_theory`
/// for a custom theory.
pub fn proof_by_evaluation(
    term: Term,
    expected: Term,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let theory = super::term_theory();
    proof_by_evaluation_in_theory(term, expected, &theory, limit)
}

pub fn proof_by_evaluation_in_theory(
    term: Term,
    expected: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let chain = evaluation_chain_in_theory(term, theory, limit)?;
    let actual = chain
        .last()
        .cloned()
        .expect("evaluation chains are nonempty");

    if !alpha_eq_term(&actual, &expected) {
        return Err(EvaluationProofError::UnexpectedNormalForm { expected, actual });
    }

    Ok(Proof::Steps(chain))
}

pub fn proof_by_reduction_in_theory(
    term: Term,
    expected: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let mut term = term;
    let mut chain = vec![term.clone()];

    if alpha_eq_term(&term, &expected) {
        return Ok(Proof::Steps(chain));
    }

    for _ in 0..limit {
        match theory.reduce(&term) {
            Step::Reduced(next) => {
                chain.push(next.clone());
                if alpha_eq_term(&next, &expected) {
                    return Ok(Proof::Steps(chain));
                }
                term = next;
            }
            Step::Normal => {
                return Err(EvaluationProofError::UnexpectedNormalForm {
                    expected,
                    actual: term,
                });
            }
        }
    }

    Err(EvaluationProofError::StepLimitExceeded { limit })
}

pub fn proof_by_same_normal_form_in_theory(
    left: Term,
    right: Term,
    theory: &Theory,
    limit: usize,
) -> Result<Proof, EvaluationProofError> {
    let left_normal = theory.normal_form(&left);
    let right_normal = theory.normal_form(&right);

    if !alpha_eq_term(&left_normal, &right_normal) {
        return Err(EvaluationProofError::UnexpectedNormalForm {
            expected: left_normal,
            actual: right_normal,
        });
    }

    let left_proof = proof_by_evaluation_in_theory(left, left_normal, theory, limit)?;
    let right_proof = proof_by_evaluation_in_theory(right, right_normal, theory, limit)?;

    Ok(Proof::Trans(
        Box::new(left_proof),
        Box::new(Proof::Symm(Box::new(right_proof))),
    ))
}

pub fn check_evaluates_to(term: Term, value: Term, proof: &Proof) -> bool {
    let theory = super::term_theory();
    check_evaluates_to_in_theory(term, value, proof, &theory)
}

pub fn check_evaluates_to_in_theory(
    term: Term,
    value: Term,
    proof: &Proof,
    theory: &Theory,
) -> bool {
    theory.check(proof, &computes_to(term, value))
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
struct ReverseProofSymbols {
    input: Symbol,
    result: Symbol,
    input_is_list_assumption: Symbol,
    accumulator_symbols: ReverseAccProofSymbols,
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

fn add_used_symbol(used: &mut Vec<Symbol>, symbol: Symbol) {
    if !used.contains(&symbol) {
        used.push(symbol);
    }
}

fn next_fresh_symbol(used: &mut Vec<Symbol>) -> Symbol {
    let mut symbol = Symbol(0);
    while used.contains(&symbol) {
        symbol = Symbol(symbol.0 + 1);
    }

    used.push(symbol);
    symbol
}

fn reverse_acc_nil_base_proof(acc: Symbol, result: Symbol, assumption: Symbol) -> Proof {
    let term = reverse_acc_call(nil(), var(acc));
    let result_body = and(computes_to(term.clone(), var(result)), is_list(var(result)));
    let theory = super::term_theory();
    let evaluation = proof_by_evaluation_in_theory(term, var(acc), &theory, 128)
        .expect("base case should reduce");

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
    let theory = super::term_theory();
    let normal = theory.normal_form(&recursive);
    let start_to_normal = proof_by_evaluation_in_theory(start, normal.clone(), &theory, 128)
        .expect("start should unfold");
    let recursive_to_normal = proof_by_evaluation_in_theory(recursive, normal, &theory, 128)
        .expect("recursive call should unfold");

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
    let start = reverse_call(var(symbols.input));
    let unfolded = apply(reverse_definition(), var(symbols.input));
    let accumulator_call = reverse_acc_call(var(symbols.input), nil());
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
        equality: Box::new(Proof::Symm(Box::new(Proof::Steps(vec![
            start,
            unfolded,
            accumulator_call,
        ])))),
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Proof, diverges, exists};

    const A: Symbol = Symbol(100);
    const B: Symbol = Symbol(101);
    const NOT_A_LIST: Symbol = Symbol(102);
    const X: Symbol = Symbol(200);
    const ACCUMULATOR: Symbol = Symbol(201);
    const RESULT: Symbol = Symbol(202);
    const HEAD: Symbol = Symbol(203);
    const TAIL: Symbol = Symbol(204);
    const ACCUMULATOR_IS_LIST: Symbol = Symbol(205);

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
    fn reverse_acc_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_ACC_COMPUTES_TO_LIST, "list");
        let acc = theorem_symbol(REVERSE_ACC_COMPUTES_TO_LIST, "acc");
        let result = theorem_symbol(REVERSE_ACC_COMPUTES_TO_LIST, "result");

        assert_eq!(
            reverse_acc_computes_to_list_source_theorem(),
            reverse_acc_computes_to_list_theorem(list, acc, result)
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
    fn reverse_source_theorem_has_expected_shape() {
        let list = theorem_symbol(REVERSE_COMPUTES_TO_LIST, "list");
        let result = theorem_symbol(REVERSE_COMPUTES_TO_LIST, "result");

        assert_eq!(
            reverse_computes_to_list_source_theorem(),
            reverse_computes_to_list_theorem(list, result)
        );
    }

    #[test]
    fn reverse_source_theorem_uses_source_proof_script() {
        assert!(matches!(
            theorem_definition(REVERSE_ACC_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
        assert!(matches!(
            theorem_definition(REVERSE_COMPUTES_TO_LIST).proof,
            ProofScript::Proof(_)
        ));
    }

    #[test]
    fn reverse_acc_nil_base_case_is_provable() {
        let theory = crate::prelude::theory();
        let theorem_base = forall(
            ACCUMULATOR,
            implies(
                is_list(var(ACCUMULATOR)),
                computes_to_list(RESULT, reverse_acc_call(nil(), var(ACCUMULATOR))),
            ),
        );

        assert!(theory.check(
            &reverse_acc_nil_base_proof(ACCUMULATOR, RESULT, ACCUMULATOR_IS_LIST),
            &theorem_base,
        ));
    }

    #[test]
    fn reverse_acc_cons_case_symbolically_unfolds() {
        let theory = crate::prelude::theory();
        let start = reverse_acc_call(cons(var(HEAD), var(TAIL)), var(ACCUMULATOR));
        let recursive = reverse_acc_call(var(TAIL), cons(var(HEAD), var(ACCUMULATOR)));
        let proof = reverse_acc_cons_unfolding_proof(HEAD, TAIL, ACCUMULATOR);

        assert!(theory.check(&proof, &computes_to(start, recursive)));
    }

    #[test]
    fn proves_reverse_acc_computes_to_list_for_all_lists() {
        let theory = crate::prelude::theory();
        let proof = reverse_acc_computes_to_list_proof(X, ACCUMULATOR, RESULT);

        assert!(theory.check(
            &proof,
            &reverse_acc_computes_to_list_theorem(X, ACCUMULATOR, RESULT),
        ));
    }

    #[test]
    fn proves_reverse_computes_to_list_for_all_lists() {
        let theory = crate::prelude::theory();
        let proof = reverse_computes_to_list_proof(X, RESULT);

        assert!(theory.check(&proof, &reverse_computes_to_list_theorem(X, RESULT)));
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
        let theory = crate::prelude::theory();
        let term = loop_forever_call();
        let proof = prove_evaluation(term.clone(), Term::Diverge);

        assert!(theory.check(&proof, &diverges(term)));
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
