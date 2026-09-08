use super::diagnostics::describe_contract_expression;
use super::*;
use crate::kernel::int32;

#[test]
fn adt_resource_parameters_report_unsupported_types_without_panicking() {
    for declaration in [
        "resource marked_cell(p: int32*, mark: Mark) { owns p[0..1]; }",
        "abstract resource marked_cell(p: int32*, mark: Mark);",
    ] {
        let source = format!("spec enum Mark {{ Clear, Set, }}\n{declaration}");
        let error = parser::parse(&source).expect_err("ADT resource indices are not supported yet");
        assert_eq!(
            error.message(),
            "resource `marked_cell` parameter `mark` uses an algebraic type; algebraic resource arguments are not supported yet"
        );
    }
}

#[test]
fn modeled_binary_tree_laws_reject_wrong_mirror_and_size() {
    let source = include_str!("../../examples/modeled-binary-tree/modeled_binary_tree.click")
        .replace("verifying \"modeled_binary_tree.c\";", "");
    verify_c0_sources(&source, &[]).expect("generic tree laws should verify");
    for (from, to) in [("right", "left"), ("left", "right")] {
        let wrong_mirror = source.replacen(
            &format!("tree_mirror({from})"),
            &format!("tree_mirror({to})"),
            1,
        );
        assert!(
            verify_c0_sources(&wrong_mirror, &[]).is_err(),
            "mirroring must not duplicate the {to} subtree"
        );
    }
    let wrong_size = source.replace(
        "ensures tree_size(tree_mirror(tree)) == tree_size(tree)",
        "ensures tree_size(tree_mirror(tree)) == Nat::Succ(tree_size(tree))",
    );
    assert!(verify_c0_sources(&wrong_size, &[]).is_err());

    let client = format!(
        "{source}\n\
         theorem nested_payload(tree: Tree<List<int32>>) {{\n\
             ensures tree_mirror(tree_mirror(tree)) == tree by {{\n\
                 apply(tree_mirror_twice(tree));\n\
             }}\n\
             ensures tree_size(tree_mirror(tree)) == tree_size(tree) by {{\n\
                 apply(tree_mirror_preserves_size(tree));\n\
             }}\n\
         }}"
    );
    verify_c0_sources(&client, &[]).expect("tree laws should apply to nested generic payloads");
}

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
        click_type: Some(ClickType::C(C0Type::Int32)),
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
