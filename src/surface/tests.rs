use super::diagnostics::describe_contract_expression;
use super::*;
use crate::kernel::int32;

const FILL3_C: &str = r#"
        int32 fill3(int32* p) {
            int32 i;
            i = 0;
            while (i < 3) {
                p[i] = i;
                i = i + 1;
            }
            return p[2];
        }
    "#;

const FILL3_CLICK: &str = r#"
        verifying "fill3.c";

        int32 fill3(int32* p) {
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures returns_second: result == 2 by auto;
        }
    "#;

fn current(expression: CExpression) -> ContractExpression {
    ContractExpression::CFragment(expression)
}

fn current_var(name: &str) -> ContractExpression {
    current(CExpression::Variable(name.to_string()))
}

fn current_int(value: u32) -> ContractExpression {
    current(CExpression::Value(int32(value)))
}

fn current_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Index(Box::new(current_var(base)), Box::new(current_int(index)))
}

#[test]
fn contract_substitution_renames_colliding_logical_binders() {
    let proposition = ClickProposition::ForAll {
        c_type: C0Type::Int32,
        name: "i".to_string(),
        body: Box::new(ClickProposition::Comparison {
            left: current_var("argument"),
            operator: ComparisonOperator::Equal,
            right: current_var("i"),
        }),
    };
    let substitutions = BTreeMap::from([(String::from("argument"), current_var("i"))]);

    let substituted = lowering::substitute_click_proposition(&proposition, &substitutions)
        .expect("surface substitution should succeed");
    let ClickProposition::ForAll { name, body, .. } = substituted else {
        panic!("substitution should preserve the logical binder");
    };
    assert_ne!(name, "i");
    assert_eq!(
        body.as_ref(),
        &ClickProposition::Comparison {
            left: current_var("i"),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::CBinding(name),
        }
    );
}

#[test]
fn contract_substitution_renames_colliding_range_fold_and_let_binders() {
    let substitutions = BTreeMap::from([(String::from("argument"), current_var("i"))]);
    let fold = ContractExpression::RangeFold {
        start: Box::new(current_int(0)),
        end: Box::new(current_int(3)),
        initial: Box::new(current_int(0)),
        accumulator: "acc".to_string(),
        item: "i".to_string(),
        body: Box::new(ContractExpression::Add(
            Box::new(current_var("argument")),
            Box::new(current_var("i")),
        )),
    };
    let let_expression = ContractExpression::Let {
        name: "i".to_string(),
        c_type: Some(C0Type::Int32),
        value: Box::new(current_int(0)),
        body: Box::new(ContractExpression::Add(
            Box::new(current_var("argument")),
            Box::new(current_var("i")),
        )),
    };

    let ContractExpression::RangeFold { item, body, .. } =
        lowering::substitute_contract_expression(&fold, &substitutions)
            .expect("range-fold substitution should succeed")
    else {
        panic!("substitution should preserve the range fold");
    };
    assert_ne!(item, "i");
    assert_eq!(
        body.as_ref(),
        &ContractExpression::Add(
            Box::new(current_var("i")),
            Box::new(ContractExpression::CBinding(item.clone())),
        )
    );

    let ContractExpression::Let { name, body, .. } =
        lowering::substitute_contract_expression(&let_expression, &substitutions)
            .expect("let substitution should succeed")
    else {
        panic!("substitution should preserve the let expression");
    };
    assert_ne!(name, "i");
    assert_eq!(
        body.as_ref(),
        &ContractExpression::Add(
            Box::new(current_var("i")),
            Box::new(ContractExpression::CBinding(name)),
        )
    );
}

fn old_index(base: &str, index: u32) -> ContractExpression {
    ContractExpression::Old(Box::new(current_index(base, index)))
}

fn ensure_comparison(
    left: ContractExpression,
    operator: ComparisonOperator,
    right: ContractExpression,
) -> Ensure {
    Ensure::Proposition(ClickProposition::Comparison {
        left,
        operator,
        right,
    })
}

mod contract_tests;
mod diagnostic_tests;
mod execution_tests;
mod expansion_tests;
mod loop_tests;
mod project_tests;
mod scaling_tests;
mod surface_syntax;
mod tactic_tests;
