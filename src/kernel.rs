use std::collections::{HashMap, HashSet};

pub type Symbol = u64;
pub type Context = HashMap<Symbol, Prop>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lambda {
    pub parameter: Symbol,
    pub body: Box<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Variant {
    pub tag: Symbol,
    pub value: Box<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Field {
    pub label: Symbol,
    pub value: Term,
}

pub type Record = Vec<Field>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaseBranch {
    pub tag: Symbol,
    pub parameter: Symbol,
    pub body: Term,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Apply {
        function: Box<Term>,
        argument: Box<Term>,
    },
    Lambda(Lambda),
    Variant(Variant),
    Record(Record),
    Project {
        record: Box<Term>,
        label: Symbol,
    },
    Case {
        variant: Box<Term>,
        branches: Vec<CaseBranch>,
    },
    Error(Box<Term>),
    Diverge,
    Var(Symbol),
    Quote(Symbol),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Step {
    Reduced(Term),
    Normal,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EvalError {
    ApplyNonLambda(Term),
    ProjectNonRecord(Term),
    MissingField(Symbol),
    CaseNonVariant(Term),
    MissingCase(Symbol),
}

pub type EvalResult<T> = Result<T, EvalError>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Prop {
    Equal(Term, Term),
    Implies(Box<Prop>, Box<Prop>),
    ForAll { variable: Symbol, body: Box<Prop> },
    Exists { variable: Symbol, body: Box<Prop> },
    And(Box<Prop>, Box<Prop>),
    Or(Box<Prop>, Box<Prop>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
    Assume(Symbol),
    Refl(Term),
    Symm(Box<Proof>),
    Trans(Box<Proof>, Box<Proof>),
    Beta {
        lambda: Lambda,
        argument: Term,
    },
    Project {
        record: Record,
        label: Symbol,
    },
    Case {
        variant: Variant,
        branches: Vec<CaseBranch>,
    },
    ImpliesIntro {
        assumption: Symbol,
        premise: Prop,
        proof: Box<Proof>,
    },
    ImpliesElim {
        implication: Box<Proof>,
        premise: Box<Proof>,
    },
    ForAllIntro {
        variable: Symbol,
        proof: Box<Proof>,
    },
    ForAllElim {
        forall: Box<Proof>,
        argument: Term,
    },
    ExistsIntro {
        variable: Symbol,
        body: Prop,
        witness: Term,
        proof: Box<Proof>,
    },
    ExistsElim {
        existential: Box<Proof>,
        witness: Symbol,
        assumption: Symbol,
        proof: Box<Proof>,
    },
    AndIntro(Box<Proof>, Box<Proof>),
    AndElimLeft(Box<Proof>),
    AndElimRight(Box<Proof>),
    OrIntroLeft {
        proof: Box<Proof>,
        right: Prop,
    },
    OrIntroRight {
        left: Prop,
        proof: Box<Proof>,
    },
    OrElim {
        disjunction: Box<Proof>,
        left_assumption: Symbol,
        left_proof: Box<Proof>,
        right_assumption: Symbol,
        right_proof: Box<Proof>,
    },
}

pub fn check(proof: &Proof, prop: &Prop) -> bool {
    check_in_context(proof, prop, &Context::new())
}

pub fn check_in_context(proof: &Proof, prop: &Prop, context: &Context) -> bool {
    proven_prop(proof, context).as_ref() == Some(prop)
}

fn proven_prop(proof: &Proof, context: &Context) -> Option<Prop> {
    match proof {
        Proof::Assume(symbol) => context.get(symbol).cloned(),
        Proof::Refl(term) => Some(Prop::Equal(term.clone(), term.clone())),
        Proof::Symm(proof) => match proven_prop(proof, context)? {
            Prop::Equal(left, right) => Some(Prop::Equal(right, left)),
            _ => None,
        },
        Proof::Trans(first, second) => {
            match (proven_prop(first, context)?, proven_prop(second, context)?) {
                (Prop::Equal(left, middle), Prop::Equal(second_middle, right))
                    if middle == second_middle =>
                {
                    Some(Prop::Equal(left, right))
                }
                _ => None,
            }
        }
        Proof::Beta { lambda, argument } => {
            if !argument_is_ready_for_beta(argument).ok()? {
                return None;
            }

            let applied = Term::Apply {
                function: Box::new(Term::Lambda(lambda.clone())),
                argument: Box::new(argument.clone()),
            };
            let reduced = substitute(lambda.body.as_ref(), lambda.parameter, argument);
            Some(Prop::Equal(applied, reduced))
        }
        Proof::Project { record, label } => {
            let projected = Term::Project {
                record: Box::new(Term::Record(record.clone())),
                label: *label,
            };
            let value = record_get(record, *label)?.clone();
            Some(Prop::Equal(projected, value))
        }
        Proof::Case { variant, branches } => {
            let cased = Term::Case {
                variant: Box::new(Term::Variant(variant.clone())),
                branches: branches.clone(),
            };
            let branch = case_branch(branches, variant.tag)?;
            let reduced = substitute(&branch.body, branch.parameter, variant.value.as_ref());
            Some(Prop::Equal(cased, reduced))
        }
        Proof::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            let conclusion = proven_prop(proof, &context)?;
            Some(Prop::Implies(
                Box::new(premise.clone()),
                Box::new(conclusion),
            ))
        }
        Proof::ImpliesElim {
            implication,
            premise,
        } => {
            let premise = proven_prop(premise, context)?;
            match proven_prop(implication, context)? {
                Prop::Implies(expected_premise, conclusion)
                    if expected_premise.as_ref() == &premise =>
                {
                    Some(*conclusion)
                }
                _ => None,
            }
        }
        Proof::ForAllIntro { variable, proof } => {
            if context_mentions_symbol(context, *variable) {
                return None;
            }
            let body = proven_prop(proof, context)?;
            Some(Prop::ForAll {
                variable: *variable,
                body: Box::new(body),
            })
        }
        Proof::ForAllElim { forall, argument } => match proven_prop(forall, context)? {
            Prop::ForAll { variable, body } => Some(substitute_prop(&body, variable, argument)),
            _ => None,
        },
        Proof::ExistsIntro {
            variable,
            body,
            witness,
            proof,
        } => {
            let witness_body = substitute_prop(body, *variable, witness);
            if proven_prop(proof, context)? == witness_body {
                Some(Prop::Exists {
                    variable: *variable,
                    body: Box::new(body.clone()),
                })
            } else {
                None
            }
        }
        Proof::ExistsElim {
            existential,
            witness,
            assumption,
            proof,
        } => match proven_prop(existential, context)? {
            Prop::Exists { variable, body } => {
                let existential = Prop::Exists {
                    variable,
                    body: body.clone(),
                };
                if prop_mentions_symbol(&existential, *witness)
                    || context_mentions_symbol(context, *witness)
                {
                    return None;
                }

                let witness_prop = substitute_prop(&body, variable, &Term::Var(*witness));
                let mut context = context.clone();
                context.insert(*assumption, witness_prop);
                let conclusion = proven_prop(proof, &context)?;

                if prop_mentions_symbol(&conclusion, *witness) {
                    None
                } else {
                    Some(conclusion)
                }
            }
            _ => None,
        },
        Proof::AndIntro(left, right) => Some(Prop::And(
            Box::new(proven_prop(left, context)?),
            Box::new(proven_prop(right, context)?),
        )),
        Proof::AndElimLeft(proof) => match proven_prop(proof, context)? {
            Prop::And(left, _) => Some(*left),
            _ => None,
        },
        Proof::AndElimRight(proof) => match proven_prop(proof, context)? {
            Prop::And(_, right) => Some(*right),
            _ => None,
        },
        Proof::OrIntroLeft { proof, right } => Some(Prop::Or(
            Box::new(proven_prop(proof, context)?),
            Box::new(right.clone()),
        )),
        Proof::OrIntroRight { left, proof } => Some(Prop::Or(
            Box::new(left.clone()),
            Box::new(proven_prop(proof, context)?),
        )),
        Proof::OrElim {
            disjunction,
            left_assumption,
            left_proof,
            right_assumption,
            right_proof,
        } => match proven_prop(disjunction, context)? {
            Prop::Or(left, right) => {
                let mut left_context = context.clone();
                left_context.insert(*left_assumption, *left);
                let left_conclusion = proven_prop(left_proof, &left_context)?;

                let mut right_context = context.clone();
                right_context.insert(*right_assumption, *right);
                let right_conclusion = proven_prop(right_proof, &right_context)?;

                if left_conclusion == right_conclusion {
                    Some(left_conclusion)
                } else {
                    None
                }
            }
            _ => None,
        },
    }
}

pub fn substitute_prop(prop: &Prop, variable: Symbol, replacement: &Term) -> Prop {
    match prop {
        Prop::Equal(left, right) => Prop::Equal(
            substitute(left, variable, replacement),
            substitute(right, variable, replacement),
        ),
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(substitute_prop(premise, variable, replacement)),
            Box::new(substitute_prop(conclusion, variable, replacement)),
        ),
        Prop::ForAll {
            variable: binder,
            body,
        } => substitute_quantified_prop(true, *binder, body, variable, replacement),
        Prop::Exists {
            variable: binder,
            body,
        } => substitute_quantified_prop(false, *binder, body, variable, replacement),
        Prop::And(left, right) => Prop::And(
            Box::new(substitute_prop(left, variable, replacement)),
            Box::new(substitute_prop(right, variable, replacement)),
        ),
        Prop::Or(left, right) => Prop::Or(
            Box::new(substitute_prop(left, variable, replacement)),
            Box::new(substitute_prop(right, variable, replacement)),
        ),
    }
}

fn substitute_quantified_prop(
    forall: bool,
    binder: Symbol,
    body: &Prop,
    variable: Symbol,
    replacement: &Term,
) -> Prop {
    if binder == variable {
        return quantified_prop(forall, binder, body.clone());
    }

    if free_symbols(replacement).contains(&binder) {
        let fresh = fresh_symbol_for_prop(body, replacement, variable);
        let body = rename_bound_var_prop(body, binder, fresh);
        return quantified_prop(forall, fresh, substitute_prop(&body, variable, replacement));
    }

    quantified_prop(forall, binder, substitute_prop(body, variable, replacement))
}

fn quantified_prop(forall: bool, variable: Symbol, body: Prop) -> Prop {
    if forall {
        Prop::ForAll {
            variable,
            body: Box::new(body),
        }
    } else {
        Prop::Exists {
            variable,
            body: Box::new(body),
        }
    }
}

pub fn free_symbols_prop(prop: &Prop) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols_prop(prop, &mut symbols);
    symbols
}

fn add_free_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_free_symbols(left, symbols);
            add_free_symbols(right, symbols);
        }
        Prop::Implies(premise, conclusion)
        | Prop::And(premise, conclusion)
        | Prop::Or(premise, conclusion) => {
            add_free_symbols_prop(premise, symbols);
            add_free_symbols_prop(conclusion, symbols);
        }
        Prop::ForAll { variable, body } | Prop::Exists { variable, body } => {
            let mut body_symbols = HashSet::new();
            add_free_symbols_prop(body, &mut body_symbols);
            body_symbols.remove(variable);
            symbols.extend(body_symbols);
        }
    }
}

fn rename_bound_var_prop(prop: &Prop, old: Symbol, new: Symbol) -> Prop {
    match prop {
        Prop::Equal(left, right) => Prop::Equal(
            rename_bound_var(left, old, new),
            rename_bound_var(right, old, new),
        ),
        Prop::Implies(premise, conclusion) => Prop::Implies(
            Box::new(rename_bound_var_prop(premise, old, new)),
            Box::new(rename_bound_var_prop(conclusion, old, new)),
        ),
        Prop::ForAll { variable, .. } if *variable == old => prop.clone(),
        Prop::ForAll { variable, body } => Prop::ForAll {
            variable: *variable,
            body: Box::new(rename_bound_var_prop(body, old, new)),
        },
        Prop::Exists { variable, .. } if *variable == old => prop.clone(),
        Prop::Exists { variable, body } => Prop::Exists {
            variable: *variable,
            body: Box::new(rename_bound_var_prop(body, old, new)),
        },
        Prop::And(left, right) => Prop::And(
            Box::new(rename_bound_var_prop(left, old, new)),
            Box::new(rename_bound_var_prop(right, old, new)),
        ),
        Prop::Or(left, right) => Prop::Or(
            Box::new(rename_bound_var_prop(left, old, new)),
            Box::new(rename_bound_var_prop(right, old, new)),
        ),
    }
}

fn fresh_symbol_for_prop(prop: &Prop, replacement: &Term, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols_prop(prop, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = 0;
    while symbols.contains(&symbol) {
        symbol += 1;
    }
    symbol
}

fn add_all_symbols_prop(prop: &Prop, symbols: &mut HashSet<Symbol>) {
    match prop {
        Prop::Equal(left, right) => {
            add_all_symbols(left, symbols);
            add_all_symbols(right, symbols);
        }
        Prop::Implies(premise, conclusion)
        | Prop::And(premise, conclusion)
        | Prop::Or(premise, conclusion) => {
            add_all_symbols_prop(premise, symbols);
            add_all_symbols_prop(conclusion, symbols);
        }
        Prop::ForAll { variable, body } | Prop::Exists { variable, body } => {
            symbols.insert(*variable);
            add_all_symbols_prop(body, symbols);
        }
    }
}

fn prop_mentions_symbol(prop: &Prop, symbol: Symbol) -> bool {
    free_symbols_prop(prop).contains(&symbol)
}

fn context_mentions_symbol(context: &Context, symbol: Symbol) -> bool {
    context
        .values()
        .any(|prop| prop_mentions_symbol(prop, symbol))
}

pub fn record_get(record: &Record, label: Symbol) -> Option<&Term> {
    record
        .iter()
        .find(|field| field.label == label)
        .map(|field| &field.value)
}

pub fn record_labels_are_unique(record: &Record) -> bool {
    let mut labels = HashSet::new();
    record.iter().all(|field| labels.insert(field.label))
}

pub fn case_branch(branches: &[CaseBranch], tag: Symbol) -> Option<&CaseBranch> {
    branches.iter().find(|branch| branch.tag == tag)
}

pub fn case_tags_are_unique(branches: &[CaseBranch]) -> bool {
    let mut tags = HashSet::new();
    branches.iter().all(|branch| tags.insert(branch.tag))
}

pub fn substitute(term: &Term, variable: Symbol, replacement: &Term) -> Term {
    match term {
        Term::Apply { function, argument } => Term::Apply {
            function: Box::new(substitute(function, variable, replacement)),
            argument: Box::new(substitute(argument, variable, replacement)),
        },
        Term::Lambda(lambda) => {
            if lambda.parameter == variable {
                return term.clone();
            }

            if free_symbols(replacement).contains(&lambda.parameter) {
                let fresh = fresh_symbol(term, replacement, variable);
                let body = rename_bound_var(lambda.body.as_ref(), lambda.parameter, fresh);
                return Term::Lambda(Lambda {
                    parameter: fresh,
                    body: Box::new(substitute(&body, variable, replacement)),
                });
            }

            Term::Lambda(Lambda {
                parameter: lambda.parameter,
                body: Box::new(substitute(lambda.body.as_ref(), variable, replacement)),
            })
        }
        Term::Var(symbol) if *symbol == variable => replacement.clone(),
        Term::Variant(variant) => Term::Variant(Variant {
            tag: variant.tag,
            value: Box::new(substitute(variant.value.as_ref(), variable, replacement)),
        }),
        Term::Record(record) => Term::Record(
            record
                .iter()
                .map(|field| Field {
                    label: field.label,
                    value: substitute(&field.value, variable, replacement),
                })
                .collect(),
        ),
        Term::Project { record, label } => Term::Project {
            record: Box::new(substitute(record, variable, replacement)),
            label: *label,
        },
        Term::Case { variant, branches } => Term::Case {
            variant: Box::new(substitute(variant, variable, replacement)),
            branches: branches
                .iter()
                .map(|branch| substitute_case_branch(branch, variable, replacement))
                .collect(),
        },
        Term::Error(error) => Term::Error(Box::new(substitute(error, variable, replacement))),
        Term::Diverge | Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

fn substitute_case_branch(branch: &CaseBranch, variable: Symbol, replacement: &Term) -> CaseBranch {
    if branch.parameter == variable {
        return branch.clone();
    }

    if free_symbols(replacement).contains(&branch.parameter) {
        let fresh = fresh_symbol(&branch.body, replacement, variable);
        let body = rename_bound_var(&branch.body, branch.parameter, fresh);
        return CaseBranch {
            tag: branch.tag,
            parameter: fresh,
            body: substitute(&body, variable, replacement),
        };
    }

    CaseBranch {
        tag: branch.tag,
        parameter: branch.parameter,
        body: substitute(&branch.body, variable, replacement),
    }
}

pub fn step(term: &Term) -> EvalResult<Step> {
    match term {
        Term::Apply { function, argument } => step_apply(function, argument),
        Term::Lambda(_) => Ok(Step::Normal),
        Term::Variant(variant) => match step(variant.value.as_ref())? {
            Step::Reduced(value) => Ok(Step::Reduced(Term::Variant(Variant {
                tag: variant.tag,
                value: Box::new(value),
            }))),
            Step::Normal if is_effect(variant.value.as_ref()) => {
                Ok(Step::Reduced(variant.value.as_ref().clone()))
            }
            Step::Normal => Ok(Step::Normal),
        },
        Term::Record(record) => step_record(record),
        Term::Project { record, label } => step_project(record, *label),
        Term::Case { variant, branches } => step_case(variant, branches),
        Term::Error(_) | Term::Diverge => Ok(Step::Normal),
        Term::Var(_) | Term::Quote(_) => Ok(Step::Normal),
    }
}

fn step_apply(function: &Term, argument: &Term) -> EvalResult<Step> {
    match function {
        Term::Lambda(lambda) => step_lambda_application(lambda, argument),
        Term::Error(_) | Term::Diverge => Ok(Step::Reduced(function.clone())),
        _ => match step(function)? {
            Step::Reduced(function) => Ok(Step::Reduced(Term::Apply {
                function: Box::new(function),
                argument: Box::new(argument.clone()),
            })),
            Step::Normal if is_known_non_callable(function) => {
                Err(EvalError::ApplyNonLambda(function.clone()))
            }
            Step::Normal => step_neutral_application(function, argument),
        },
    }
}

fn step_lambda_application(lambda: &Lambda, argument: &Term) -> EvalResult<Step> {
    match step(argument)? {
        Step::Reduced(argument) => Ok(Step::Reduced(Term::Apply {
            function: Box::new(Term::Lambda(lambda.clone())),
            argument: Box::new(argument),
        })),
        Step::Normal if is_effect(argument) => Ok(Step::Reduced(argument.clone())),
        Step::Normal => Ok(Step::Reduced(substitute(
            lambda.body.as_ref(),
            lambda.parameter,
            argument,
        ))),
    }
}

fn step_neutral_application(function: &Term, argument: &Term) -> EvalResult<Step> {
    match step(argument)? {
        Step::Reduced(argument) => Ok(Step::Reduced(Term::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument),
        })),
        Step::Normal if is_effect(argument) => Ok(Step::Reduced(argument.clone())),
        Step::Normal => Ok(Step::Normal),
    }
}

fn argument_is_ready_for_beta(argument: &Term) -> EvalResult<bool> {
    match step(argument)? {
        Step::Reduced(_) => Ok(false),
        Step::Normal => Ok(!is_effect(argument)),
    }
}

fn is_effect(term: &Term) -> bool {
    matches!(term, Term::Error(_) | Term::Diverge)
}

fn is_known_non_callable(term: &Term) -> bool {
    matches!(term, Term::Quote(_) | Term::Variant(_) | Term::Record(_))
}

fn step_record(record: &Record) -> EvalResult<Step> {
    for (index, field) in record.iter().enumerate() {
        match step(&field.value)? {
            Step::Reduced(value) => {
                let mut record = record.clone();
                record[index].value = value;
                return Ok(Step::Reduced(Term::Record(record)));
            }
            Step::Normal if is_effect(&field.value) => {
                return Ok(Step::Reduced(field.value.clone()));
            }
            Step::Normal => {}
        }
    }
    Ok(Step::Normal)
}

fn step_project(record: &Term, label: Symbol) -> EvalResult<Step> {
    match step(record)? {
        Step::Reduced(record) => Ok(Step::Reduced(Term::Project {
            record: Box::new(record),
            label,
        })),
        Step::Normal => match record {
            Term::Record(fields) => record_get(fields, label)
                .cloned()
                .map(Step::Reduced)
                .ok_or(EvalError::MissingField(label)),
            Term::Error(_) | Term::Diverge => Ok(Step::Reduced(record.clone())),
            Term::Var(_) | Term::Apply { .. } | Term::Project { .. } | Term::Case { .. } => {
                Ok(Step::Normal)
            }
            Term::Quote(_) | Term::Lambda(_) | Term::Variant(_) => {
                Err(EvalError::ProjectNonRecord(record.clone()))
            }
        },
    }
}

fn step_case(variant: &Term, branches: &[CaseBranch]) -> EvalResult<Step> {
    match step(variant)? {
        Step::Reduced(variant) => Ok(Step::Reduced(Term::Case {
            variant: Box::new(variant),
            branches: branches.to_vec(),
        })),
        Step::Normal => match variant {
            Term::Variant(variant) => {
                let branch = case_branch(branches, variant.tag)
                    .ok_or(EvalError::MissingCase(variant.tag))?;
                Ok(Step::Reduced(substitute(
                    &branch.body,
                    branch.parameter,
                    variant.value.as_ref(),
                )))
            }
            Term::Error(_) | Term::Diverge => Ok(Step::Reduced(variant.clone())),
            Term::Var(_) | Term::Apply { .. } | Term::Project { .. } | Term::Case { .. } => {
                Ok(Step::Normal)
            }
            Term::Quote(_) | Term::Lambda(_) | Term::Record(_) => {
                Err(EvalError::CaseNonVariant(variant.clone()))
            }
        },
    }
}

pub fn normal_form(term: &Term) -> EvalResult<Term> {
    let mut term = term.clone();
    loop {
        match step(&term)? {
            Step::Reduced(next) => term = next,
            Step::Normal => return Ok(term),
        }
    }
}

pub fn free_symbols(term: &Term) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols(term, &mut symbols);
    symbols
}

fn add_free_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
    match term {
        Term::Apply { function, argument } => {
            add_free_symbols(function, symbols);
            add_free_symbols(argument, symbols);
        }
        Term::Lambda(lambda) => {
            let mut body_symbols = HashSet::new();
            add_free_symbols(lambda.body.as_ref(), &mut body_symbols);
            body_symbols.remove(&lambda.parameter);
            symbols.extend(body_symbols);
        }
        Term::Variant(variant) => {
            add_free_symbols(variant.value.as_ref(), symbols);
        }
        Term::Record(record) => {
            for field in record {
                add_free_symbols(&field.value, symbols);
            }
        }
        Term::Project { record, .. } => {
            add_free_symbols(record, symbols);
        }
        Term::Case { variant, branches } => {
            add_free_symbols(variant, symbols);
            for branch in branches {
                let mut body_symbols = HashSet::new();
                add_free_symbols(&branch.body, &mut body_symbols);
                body_symbols.remove(&branch.parameter);
                symbols.extend(body_symbols);
            }
        }
        Term::Error(error) => {
            add_free_symbols(error, symbols);
        }
        Term::Diverge => {}
        Term::Var(symbol) => {
            symbols.insert(*symbol);
        }
        Term::Quote(_) => {}
    }
}

fn rename_bound_var(term: &Term, old: Symbol, new: Symbol) -> Term {
    match term {
        Term::Apply { function, argument } => Term::Apply {
            function: Box::new(rename_bound_var(function, old, new)),
            argument: Box::new(rename_bound_var(argument, old, new)),
        },
        Term::Lambda(lambda) if lambda.parameter == old => Term::Lambda(lambda.clone()),
        Term::Lambda(lambda) => Term::Lambda(Lambda {
            parameter: lambda.parameter,
            body: Box::new(rename_bound_var(lambda.body.as_ref(), old, new)),
        }),
        Term::Variant(variant) => Term::Variant(Variant {
            tag: variant.tag,
            value: Box::new(rename_bound_var(variant.value.as_ref(), old, new)),
        }),
        Term::Record(record) => Term::Record(
            record
                .iter()
                .map(|field| Field {
                    label: field.label,
                    value: rename_bound_var(&field.value, old, new),
                })
                .collect(),
        ),
        Term::Project { record, label } => Term::Project {
            record: Box::new(rename_bound_var(record, old, new)),
            label: *label,
        },
        Term::Case { variant, branches } => Term::Case {
            variant: Box::new(rename_bound_var(variant, old, new)),
            branches: branches
                .iter()
                .map(|branch| {
                    if branch.parameter == old {
                        branch.clone()
                    } else {
                        CaseBranch {
                            tag: branch.tag,
                            parameter: branch.parameter,
                            body: rename_bound_var(&branch.body, old, new),
                        }
                    }
                })
                .collect(),
        },
        Term::Error(error) => Term::Error(Box::new(rename_bound_var(error, old, new))),
        Term::Diverge => term.clone(),
        Term::Var(symbol) if *symbol == old => Term::Var(new),
        Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

fn fresh_symbol(term: &Term, replacement: &Term, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols(term, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = 0;
    while symbols.contains(&symbol) {
        symbol += 1;
    }
    symbol
}

fn add_all_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
    match term {
        Term::Apply { function, argument } => {
            add_all_symbols(function, symbols);
            add_all_symbols(argument, symbols);
        }
        Term::Lambda(lambda) => {
            symbols.insert(lambda.parameter);
            add_all_symbols(lambda.body.as_ref(), symbols);
        }
        Term::Variant(variant) => {
            symbols.insert(variant.tag);
            add_all_symbols(variant.value.as_ref(), symbols);
        }
        Term::Record(record) => {
            for field in record {
                symbols.insert(field.label);
                add_all_symbols(&field.value, symbols);
            }
        }
        Term::Project { record, label } => {
            symbols.insert(*label);
            add_all_symbols(record, symbols);
        }
        Term::Case { variant, branches } => {
            add_all_symbols(variant, symbols);
            for branch in branches {
                symbols.insert(branch.tag);
                symbols.insert(branch.parameter);
                add_all_symbols(&branch.body, symbols);
            }
        }
        Term::Error(error) => {
            add_all_symbols(error, symbols);
        }
        Term::Diverge => {}
        Term::Var(symbol) | Term::Quote(symbol) => {
            symbols.insert(*symbol);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lambda(parameter: Symbol, body: Term) -> Term {
        Term::Lambda(Lambda {
            parameter,
            body: Box::new(body),
        })
    }

    fn apply(function: Term, argument: Term) -> Term {
        Term::Apply {
            function: Box::new(function),
            argument: Box::new(argument),
        }
    }

    fn variant(tag: Symbol, value: Term) -> Term {
        Term::Variant(Variant {
            tag,
            value: Box::new(value),
        })
    }

    fn field(label: Symbol, value: Term) -> Field {
        Field { label, value }
    }

    fn record(fields: Vec<Field>) -> Term {
        Term::Record(fields)
    }

    fn project(record: Term, label: Symbol) -> Term {
        Term::Project {
            record: Box::new(record),
            label,
        }
    }

    fn branch(tag: Symbol, parameter: Symbol, body: Term) -> CaseBranch {
        CaseBranch {
            tag,
            parameter,
            body,
        }
    }

    fn case(variant: Term, branches: Vec<CaseBranch>) -> Term {
        Term::Case {
            variant: Box::new(variant),
            branches,
        }
    }

    fn error(error: Term) -> Term {
        Term::Error(Box::new(error))
    }

    fn equal(left: Term, right: Term) -> Prop {
        Prop::Equal(left, right)
    }

    fn implies(premise: Prop, conclusion: Prop) -> Prop {
        Prop::Implies(Box::new(premise), Box::new(conclusion))
    }

    fn forall(variable: Symbol, body: Prop) -> Prop {
        Prop::ForAll {
            variable,
            body: Box::new(body),
        }
    }

    fn exists(variable: Symbol, body: Prop) -> Prop {
        Prop::Exists {
            variable,
            body: Box::new(body),
        }
    }

    fn prop_and(left: Prop, right: Prop) -> Prop {
        Prop::And(Box::new(left), Box::new(right))
    }

    fn prop_or(left: Prop, right: Prop) -> Prop {
        Prop::Or(Box::new(left), Box::new(right))
    }

    #[test]
    fn step_beta_reduces_identity_lambda() {
        let term = apply(lambda(1, Term::Var(1)), Term::Quote(2));

        assert_eq!(step(&term), Ok(Step::Reduced(Term::Quote(2))));
    }

    #[test]
    fn application_reduces_argument_before_beta() {
        let term = apply(
            lambda(1, Term::Quote(9)),
            apply(lambda(2, Term::Var(2)), Term::Quote(3)),
        );

        assert_eq!(
            step(&term),
            Ok(Step::Reduced(apply(
                lambda(1, Term::Quote(9)),
                Term::Quote(3)
            )))
        );
        assert_eq!(normal_form(&term), Ok(Term::Quote(9)));
    }

    #[test]
    fn lambda_is_a_value_without_evaluating_its_body() {
        let term = lambda(1, apply(lambda(2, Term::Var(2)), Term::Var(1)));

        assert_eq!(step(&term), Ok(Step::Normal));
    }

    #[test]
    fn application_substitutes_lambda_arguments_without_evaluating_their_bodies() {
        let argument = lambda(2, apply(lambda(3, Term::Var(3)), Term::Var(2)));
        let term = apply(lambda(1, Term::Var(1)), argument.clone());

        assert_eq!(step(&term), Ok(Step::Reduced(argument)));
    }

    #[test]
    fn step_distinguishes_normal_terms_from_errors() {
        assert_eq!(step(&Term::Quote(1)), Ok(Step::Normal));
        assert_eq!(step(&apply(Term::Var(1), Term::Quote(2))), Ok(Step::Normal));
    }

    #[test]
    fn step_errors_on_known_non_callable_application() {
        let term = apply(Term::Quote(1), Term::Quote(2));

        assert_eq!(step(&term), Err(EvalError::ApplyNonLambda(Term::Quote(1))));
        assert_eq!(
            normal_form(&term),
            Err(EvalError::ApplyNonLambda(Term::Quote(1)))
        );
    }

    #[test]
    fn error_and_diverge_are_normal_terms() {
        assert_eq!(step(&error(Term::Quote(1))), Ok(Step::Normal));
        assert_eq!(step(&Term::Diverge), Ok(Step::Normal));
    }

    #[test]
    fn application_propagates_error_and_diverge_function() {
        let thrown = error(Term::Quote(1));
        let error_application = apply(thrown.clone(), Term::Quote(2));
        let diverging_application = apply(Term::Diverge, Term::Quote(2));

        assert_eq!(step(&error_application), Ok(Step::Reduced(thrown.clone())));
        assert_eq!(normal_form(&error_application), Ok(thrown));
        assert_eq!(
            step(&diverging_application),
            Ok(Step::Reduced(Term::Diverge))
        );
        assert_eq!(normal_form(&diverging_application), Ok(Term::Diverge));
    }

    #[test]
    fn application_propagates_error_and_diverge_argument_before_beta() {
        let thrown = error(Term::Quote(1));
        let error_application = apply(lambda(2, Term::Quote(3)), thrown.clone());
        let diverging_application = apply(lambda(2, Term::Quote(3)), Term::Diverge);

        assert_eq!(step(&error_application), Ok(Step::Reduced(thrown.clone())));
        assert_eq!(normal_form(&error_application), Ok(thrown));
        assert_eq!(
            step(&diverging_application),
            Ok(Step::Reduced(Term::Diverge))
        );
        assert_eq!(normal_form(&diverging_application), Ok(Term::Diverge));
    }

    #[test]
    fn neutral_application_still_evaluates_argument_effects() {
        let thrown = error(Term::Quote(1));

        assert_eq!(
            step(&apply(Term::Var(2), thrown.clone())),
            Ok(Step::Reduced(thrown))
        );
        assert_eq!(
            step(&apply(Term::Var(2), Term::Diverge)),
            Ok(Step::Reduced(Term::Diverge))
        );
    }

    #[test]
    fn application_reports_argument_errors_before_beta() {
        let term = apply(
            lambda(1, Term::Quote(2)),
            project(record(vec![field(3, Term::Quote(4))]), 5),
        );

        assert_eq!(step(&term), Err(EvalError::MissingField(5)));
    }

    #[test]
    fn normal_form_reduces_repeatedly() {
        let term = apply(
            lambda(1, apply(lambda(2, Term::Var(2)), Term::Var(1))),
            Term::Quote(3),
        );

        assert_eq!(normal_form(&term), Ok(Term::Quote(3)));
    }

    #[test]
    fn record_get_returns_first_matching_field() {
        let record = vec![
            field(1, Term::Quote(10)),
            field(2, Term::Quote(20)),
            field(1, Term::Quote(30)),
        ];

        assert_eq!(record_get(&record, 1).cloned(), Some(Term::Quote(10)));
        assert_eq!(record_get(&record, 2).cloned(), Some(Term::Quote(20)));
        assert_eq!(record_get(&record, 3), None);
    }

    #[test]
    fn record_labels_are_unique_detects_duplicates() {
        assert!(record_labels_are_unique(&vec![
            field(1, Term::Quote(10)),
            field(2, Term::Quote(20)),
        ]));
        assert!(!record_labels_are_unique(&vec![
            field(1, Term::Quote(10)),
            field(1, Term::Quote(20)),
        ]));
    }

    #[test]
    fn substitution_descends_into_variants_and_records() {
        let term = record(vec![field(1, variant(2, Term::Var(3)))]);

        assert_eq!(
            substitute(&term, 3, &Term::Quote(4)),
            record(vec![field(1, variant(2, Term::Quote(4)))])
        );
    }

    #[test]
    fn substitution_descends_into_error_payload() {
        let term = error(Term::Var(1));

        assert_eq!(substitute(&term, 1, &Term::Quote(2)), error(Term::Quote(2)));
    }

    #[test]
    fn step_reduces_inside_variant_payload() {
        let term = variant(1, apply(lambda(2, Term::Var(2)), Term::Quote(3)));

        assert_eq!(step(&term), Ok(Step::Reduced(variant(1, Term::Quote(3)))));
    }

    #[test]
    fn variant_propagates_error_and_diverge_payload() {
        let thrown = error(Term::Quote(1));

        assert_eq!(step(&variant(2, thrown.clone())), Ok(Step::Reduced(thrown)));
        assert_eq!(
            step(&variant(2, Term::Diverge)),
            Ok(Step::Reduced(Term::Diverge))
        );
    }

    #[test]
    fn step_reduces_first_reducible_record_field() {
        let term = record(vec![
            field(1, Term::Quote(1)),
            field(2, apply(lambda(3, Term::Var(3)), Term::Quote(4))),
            field(3, apply(lambda(5, Term::Var(5)), Term::Quote(6))),
        ]);

        assert_eq!(
            step(&term),
            Ok(Step::Reduced(record(vec![
                field(1, Term::Quote(1)),
                field(2, Term::Quote(4)),
                field(3, apply(lambda(5, Term::Var(5)), Term::Quote(6))),
            ])))
        );
    }

    #[test]
    fn record_propagates_error_and_diverge_fields() {
        let thrown = error(Term::Quote(1));
        let error_record = record(vec![field(1, Term::Quote(2)), field(3, thrown.clone())]);
        let diverging_record = record(vec![field(1, Term::Quote(2)), field(3, Term::Diverge)]);

        assert_eq!(step(&error_record), Ok(Step::Reduced(thrown)));
        assert_eq!(step(&diverging_record), Ok(Step::Reduced(Term::Diverge)));
    }

    #[test]
    fn record_reduces_earlier_field_before_later_effect() {
        let thrown = error(Term::Quote(1));
        let term = record(vec![
            field(1, apply(lambda(2, Term::Var(2)), Term::Quote(3))),
            field(4, thrown.clone()),
        ]);

        assert_eq!(
            step(&term),
            Ok(Step::Reduced(record(vec![
                field(1, Term::Quote(3)),
                field(4, thrown)
            ])))
        );
    }

    #[test]
    fn project_gets_present_record_field() {
        let term = project(
            record(vec![field(1, Term::Quote(10)), field(2, Term::Quote(20))]),
            2,
        );

        assert_eq!(step(&term), Ok(Step::Reduced(Term::Quote(20))));
    }

    #[test]
    fn project_reduces_record_expression_first() {
        let term = project(
            apply(
                lambda(1, record(vec![field(2, Term::Var(1))])),
                Term::Quote(30),
            ),
            2,
        );

        assert_eq!(
            step(&term),
            Ok(Step::Reduced(project(
                record(vec![field(2, Term::Quote(30))]),
                2
            )))
        );
        assert_eq!(normal_form(&term), Ok(Term::Quote(30)));
    }

    #[test]
    fn project_missing_field_errors() {
        let term = project(record(vec![field(1, Term::Quote(10))]), 2);

        assert_eq!(step(&term), Err(EvalError::MissingField(2)));
    }

    #[test]
    fn project_known_non_record_errors() {
        let term = project(Term::Quote(10), 2);

        assert_eq!(
            step(&term),
            Err(EvalError::ProjectNonRecord(Term::Quote(10)))
        );
    }

    #[test]
    fn project_open_record_is_neutral() {
        let term = project(Term::Var(1), 2);

        assert_eq!(step(&term), Ok(Step::Normal));
    }

    #[test]
    fn project_propagates_error_and_diverge_record() {
        let thrown = error(Term::Quote(1));
        let error_projection = project(thrown.clone(), 2);
        let diverging_projection = project(Term::Diverge, 2);

        assert_eq!(step(&error_projection), Ok(Step::Reduced(thrown)));
        assert_eq!(
            step(&diverging_projection),
            Ok(Step::Reduced(Term::Diverge))
        );
    }

    #[test]
    fn substitution_descends_into_projection_record() {
        let term = project(Term::Var(1), 2);

        assert_eq!(
            substitute(&term, 1, &Term::Var(3)),
            project(Term::Var(3), 2)
        );
    }

    #[test]
    fn case_branch_returns_first_matching_branch() {
        let branches = vec![
            branch(1, 10, Term::Quote(10)),
            branch(2, 20, Term::Quote(20)),
            branch(1, 30, Term::Quote(30)),
        ];

        assert_eq!(case_branch(&branches, 1), Some(&branches[0]));
        assert_eq!(case_branch(&branches, 2), Some(&branches[1]));
        assert_eq!(case_branch(&branches, 3), None);
    }

    #[test]
    fn case_tags_are_unique_detects_duplicates() {
        assert!(case_tags_are_unique(&vec![
            branch(1, 10, Term::Quote(10)),
            branch(2, 20, Term::Quote(20)),
        ]));
        assert!(!case_tags_are_unique(&vec![
            branch(1, 10, Term::Quote(10)),
            branch(1, 20, Term::Quote(20)),
        ]));
    }

    #[test]
    fn case_reduces_matching_variant_branch() {
        let term = case(
            variant(1, Term::Quote(10)),
            vec![branch(1, 2, Term::Var(2)), branch(3, 4, Term::Var(4))],
        );

        assert_eq!(step(&term), Ok(Step::Reduced(Term::Quote(10))));
    }

    #[test]
    fn case_reduces_variant_expression_first() {
        let term = case(
            apply(lambda(1, variant(2, Term::Var(1))), Term::Quote(30)),
            vec![branch(2, 3, Term::Var(3))],
        );

        assert_eq!(
            step(&term),
            Ok(Step::Reduced(case(
                variant(2, Term::Quote(30)),
                vec![branch(2, 3, Term::Var(3))]
            )))
        );
        assert_eq!(normal_form(&term), Ok(Term::Quote(30)));
    }

    #[test]
    fn case_missing_branch_errors() {
        let term = case(
            variant(1, Term::Quote(10)),
            vec![branch(2, 3, Term::Var(3))],
        );

        assert_eq!(step(&term), Err(EvalError::MissingCase(1)));
    }

    #[test]
    fn case_known_non_variant_errors() {
        let term = case(Term::Quote(10), vec![branch(1, 2, Term::Var(2))]);

        assert_eq!(step(&term), Err(EvalError::CaseNonVariant(Term::Quote(10))));
    }

    #[test]
    fn case_open_variant_is_neutral() {
        let term = case(Term::Var(1), vec![branch(2, 3, Term::Var(3))]);

        assert_eq!(step(&term), Ok(Step::Normal));
    }

    #[test]
    fn case_propagates_error_and_diverge_variant() {
        let thrown = error(Term::Quote(1));
        let error_case = case(thrown.clone(), vec![branch(1, 2, Term::Var(2))]);
        let diverging_case = case(Term::Diverge, vec![branch(1, 2, Term::Var(2))]);

        assert_eq!(step(&error_case), Ok(Step::Reduced(thrown)));
        assert_eq!(step(&diverging_case), Ok(Step::Reduced(Term::Diverge)));
    }

    #[test]
    fn substitution_descends_into_case_variant_and_branches() {
        let term = case(
            Term::Var(1),
            vec![branch(2, 3, apply(Term::Var(3), Term::Var(4)))],
        );

        assert_eq!(
            substitute(&term, 4, &Term::Quote(5)),
            case(
                Term::Var(1),
                vec![branch(2, 3, apply(Term::Var(3), Term::Quote(5)))]
            )
        );
    }

    #[test]
    fn substitution_avoids_case_branch_capture() {
        let term = case(Term::Var(1), vec![branch(2, 3, Term::Var(4))]);

        assert_eq!(
            substitute(&term, 4, &Term::Var(3)),
            case(Term::Var(1), vec![branch(2, 0, Term::Var(3))])
        );
    }

    #[test]
    fn substitution_respects_shadowing() {
        let term = lambda(1, Term::Var(1));

        assert_eq!(substitute(&term, 1, &Term::Quote(2)), term);
    }

    #[test]
    fn substitution_avoids_variable_capture() {
        let term = lambda(2, Term::Var(1));

        assert_eq!(substitute(&term, 1, &Term::Var(2)), lambda(0, Term::Var(2)));
    }

    #[test]
    fn free_symbols_ignores_bound_symbols_and_quotes() {
        assert_eq!(
            free_symbols(&lambda(1, apply(Term::Var(1), Term::Quote(2)))),
            HashSet::new()
        );
    }

    #[test]
    fn free_symbols_keep_sibling_occurrences() {
        assert_eq!(
            free_symbols(&apply(Term::Var(1), lambda(1, Term::Var(1)))),
            HashSet::from([1])
        );
    }

    #[test]
    fn free_symbols_ignore_variant_tags_and_record_labels() {
        assert_eq!(
            free_symbols(&case(
                project(record(vec![field(100, variant(200, Term::Var(1)))]), 300,),
                vec![branch(400, 2, apply(Term::Var(2), Term::Var(3)))]
            )),
            HashSet::from([1, 3])
        );
    }

    #[test]
    fn free_symbols_include_error_payload_and_ignore_diverge() {
        assert_eq!(
            free_symbols(&record(vec![
                field(1, error(Term::Var(2))),
                field(3, Term::Diverge),
            ])),
            HashSet::from([2])
        );
    }

    #[test]
    fn substitute_prop_avoids_quantifier_capture() {
        let prop = forall(2, equal(Term::Var(1), Term::Var(2)));

        assert_eq!(
            substitute_prop(&prop, 1, &Term::Var(2)),
            forall(0, equal(Term::Var(2), Term::Var(0)))
        );
    }

    #[test]
    fn free_symbols_prop_keep_sibling_occurrences() {
        assert_eq!(
            free_symbols_prop(&prop_and(
                equal(Term::Var(1), Term::Var(1)),
                forall(1, equal(Term::Var(1), Term::Var(1))),
            )),
            HashSet::from([1])
        );
    }

    #[test]
    fn refl_proves_term_equal_to_itself() {
        let term = Term::Quote(1);

        assert!(check(
            &Proof::Refl(term.clone()),
            &Prop::Equal(term.clone(), term)
        ));
    }

    #[test]
    fn symm_flips_equality() {
        let proof = Proof::Symm(Box::new(Proof::Beta {
            lambda: Lambda {
                parameter: 1,
                body: Box::new(Term::Var(1)),
            },
            argument: Term::Quote(2),
        }));

        assert!(check(
            &proof,
            &Prop::Equal(
                Term::Quote(2),
                apply(lambda(1, Term::Var(1)), Term::Quote(2))
            )
        ));
    }

    #[test]
    fn trans_chains_matching_equalities() {
        let lambda = Lambda {
            parameter: 1,
            body: Box::new(Term::Var(1)),
        };
        let argument = Term::Quote(2);
        let applied = apply(Term::Lambda(lambda.clone()), argument.clone());
        let proof = Proof::Trans(
            Box::new(Proof::Beta {
                lambda,
                argument: argument.clone(),
            }),
            Box::new(Proof::Refl(argument.clone())),
        );

        assert!(check(&proof, &Prop::Equal(applied, argument)));
    }

    #[test]
    fn trans_rejects_mismatched_middle_terms() {
        let proof = Proof::Trans(
            Box::new(Proof::Refl(Term::Quote(1))),
            Box::new(Proof::Refl(Term::Quote(2))),
        );

        assert!(!check(&proof, &Prop::Equal(Term::Quote(1), Term::Quote(2))));
    }

    #[test]
    fn beta_proves_application_equal_to_substituted_body() {
        let lambda = Lambda {
            parameter: 1,
            body: Box::new(Term::Var(1)),
        };
        let argument = Term::Quote(2);

        assert!(check(
            &Proof::Beta {
                lambda: lambda.clone(),
                argument: argument.clone()
            },
            &Prop::Equal(apply(Term::Lambda(lambda), argument), Term::Quote(2))
        ));
    }

    #[test]
    fn beta_proof_rejects_reducible_arguments() {
        let lam = Lambda {
            parameter: 1,
            body: Box::new(Term::Quote(9)),
        };
        let argument = apply(lambda(2, Term::Var(2)), Term::Quote(3));

        assert!(!check(
            &Proof::Beta {
                lambda: lam.clone(),
                argument: argument.clone()
            },
            &Prop::Equal(apply(Term::Lambda(lam), argument), Term::Quote(9))
        ));
    }

    #[test]
    fn beta_proof_rejects_effect_arguments() {
        let lambda = Lambda {
            parameter: 1,
            body: Box::new(Term::Quote(9)),
        };
        let thrown = error(Term::Quote(2));

        assert!(!check(
            &Proof::Beta {
                lambda: lambda.clone(),
                argument: thrown.clone()
            },
            &Prop::Equal(apply(Term::Lambda(lambda), thrown), Term::Quote(9))
        ));
    }

    #[test]
    fn project_proof_proves_projection_equal_to_field_value() {
        let record = vec![field(1, Term::Quote(10)), field(2, Term::Quote(20))];

        assert!(check(
            &Proof::Project {
                record: record.clone(),
                label: 2
            },
            &Prop::Equal(project(Term::Record(record), 2), Term::Quote(20))
        ));
    }

    #[test]
    fn project_proof_with_missing_field_proves_nothing() {
        let record = vec![field(1, Term::Quote(10))];

        assert!(!check(
            &Proof::Project { record, label: 2 },
            &Prop::Equal(Term::Quote(1), Term::Quote(1))
        ));
    }

    #[test]
    fn case_proof_proves_case_equal_to_selected_branch() {
        let variant = Variant {
            tag: 1,
            value: Box::new(Term::Quote(10)),
        };
        let branches = vec![branch(1, 2, Term::Var(2)), branch(3, 4, Term::Var(4))];

        assert!(check(
            &Proof::Case {
                variant: variant.clone(),
                branches: branches.clone(),
            },
            &Prop::Equal(case(Term::Variant(variant), branches), Term::Quote(10))
        ));
    }

    #[test]
    fn case_proof_with_missing_branch_proves_nothing() {
        let variant = Variant {
            tag: 1,
            value: Box::new(Term::Quote(10)),
        };
        let branches = vec![branch(2, 3, Term::Var(3))];

        assert!(!check(
            &Proof::Case { variant, branches },
            &Prop::Equal(Term::Quote(1), Term::Quote(1))
        ));
    }

    #[test]
    fn assume_uses_context() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let mut context = Context::new();
        context.insert(7, prop.clone());

        assert!(check_in_context(&Proof::Assume(7), &prop, &context));
        assert!(!check(&Proof::Assume(7), &prop));
    }

    #[test]
    fn implies_intro_proves_assumption_implies_itself() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let proof = Proof::ImpliesIntro {
            assumption: 7,
            premise: prop.clone(),
            proof: Box::new(Proof::Assume(7)),
        };

        assert!(check(&proof, &implies(prop.clone(), prop)));
    }

    #[test]
    fn implies_elim_applies_implication() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let proof = Proof::ImpliesElim {
            implication: Box::new(Proof::ImpliesIntro {
                assumption: 7,
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(7)),
            }),
            premise: Box::new(Proof::Refl(Term::Quote(1))),
        };

        assert!(check(&proof, &prop));
    }

    #[test]
    fn implies_elim_rejects_mismatched_premise() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let other = equal(Term::Quote(2), Term::Quote(2));
        let proof = Proof::ImpliesElim {
            implication: Box::new(Proof::ImpliesIntro {
                assumption: 7,
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(7)),
            }),
            premise: Box::new(Proof::Refl(Term::Quote(2))),
        };

        assert!(!check(&proof, &prop));
        assert!(!check(&proof, &other));
    }

    #[test]
    fn forall_intro_generalizes_variable_not_free_in_context() {
        let proof = Proof::ForAllIntro {
            variable: 1,
            proof: Box::new(Proof::Refl(Term::Var(1))),
        };

        assert!(check(&proof, &forall(1, equal(Term::Var(1), Term::Var(1)))));
    }

    #[test]
    fn forall_intro_rejects_variable_free_in_context() {
        let prop = equal(Term::Var(1), Term::Var(1));
        let proof = Proof::ForAllIntro {
            variable: 1,
            proof: Box::new(Proof::Assume(7)),
        };
        let mut context = Context::new();
        context.insert(7, prop.clone());

        assert!(!check_in_context(&proof, &forall(1, prop), &context));
    }

    #[test]
    fn forall_elim_instantiates_body() {
        let proof = Proof::ForAllElim {
            forall: Box::new(Proof::ForAllIntro {
                variable: 1,
                proof: Box::new(Proof::Refl(Term::Var(1))),
            }),
            argument: Term::Quote(2),
        };

        assert!(check(&proof, &equal(Term::Quote(2), Term::Quote(2))));
    }

    #[test]
    fn exists_intro_uses_witness() {
        let body = equal(Term::Var(1), Term::Var(1));
        let proof = Proof::ExistsIntro {
            variable: 1,
            body: body.clone(),
            witness: Term::Quote(2),
            proof: Box::new(Proof::Refl(Term::Quote(2))),
        };

        assert!(check(&proof, &exists(1, body)));
    }

    #[test]
    fn exists_elim_accepts_nonescaping_witness() {
        let body = equal(Term::Var(1), Term::Var(1));
        let conclusion = equal(Term::Quote(0), Term::Quote(0));
        let proof = Proof::ExistsElim {
            existential: Box::new(Proof::ExistsIntro {
                variable: 1,
                body,
                witness: Term::Quote(2),
                proof: Box::new(Proof::Refl(Term::Quote(2))),
            }),
            witness: 9,
            assumption: 7,
            proof: Box::new(Proof::Refl(Term::Quote(0))),
        };

        assert!(check(&proof, &conclusion));
    }

    #[test]
    fn exists_elim_rejects_escaping_witness() {
        let body = equal(Term::Var(1), Term::Var(1));
        let conclusion = equal(Term::Var(9), Term::Var(9));
        let proof = Proof::ExistsElim {
            existential: Box::new(Proof::ExistsIntro {
                variable: 1,
                body,
                witness: Term::Quote(2),
                proof: Box::new(Proof::Refl(Term::Quote(2))),
            }),
            witness: 9,
            assumption: 7,
            proof: Box::new(Proof::Assume(7)),
        };

        assert!(!check(&proof, &conclusion));
    }

    #[test]
    fn and_intro_and_elim_work() {
        let left = equal(Term::Quote(1), Term::Quote(1));
        let right = equal(Term::Quote(2), Term::Quote(2));
        let proof = Proof::AndIntro(
            Box::new(Proof::Refl(Term::Quote(1))),
            Box::new(Proof::Refl(Term::Quote(2))),
        );

        assert!(check(&proof, &prop_and(left.clone(), right.clone())));
        assert!(check(&Proof::AndElimLeft(Box::new(proof.clone())), &left));
        assert!(check(&Proof::AndElimRight(Box::new(proof)), &right));
    }

    #[test]
    fn or_intro_and_elim_work() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let proof = Proof::OrElim {
            disjunction: Box::new(Proof::OrIntroLeft {
                proof: Box::new(Proof::Refl(Term::Quote(1))),
                right: prop.clone(),
            }),
            left_assumption: 7,
            left_proof: Box::new(Proof::Assume(7)),
            right_assumption: 8,
            right_proof: Box::new(Proof::Assume(8)),
        };

        assert!(check(&proof, &prop));
    }

    #[test]
    fn or_elim_rejects_mismatched_case_conclusions() {
        let left = equal(Term::Quote(1), Term::Quote(1));
        let right = equal(Term::Quote(2), Term::Quote(2));
        let proof = Proof::OrElim {
            disjunction: Box::new(Proof::OrIntroRight {
                left: left.clone(),
                proof: Box::new(Proof::Refl(Term::Quote(2))),
            }),
            left_assumption: 7,
            left_proof: Box::new(Proof::Assume(7)),
            right_assumption: 8,
            right_proof: Box::new(Proof::Assume(8)),
        };

        assert!(!check(&proof, &prop_or(left, right)));
    }
}
