use super::diagnostics::describe_contract_expression;
use super::*;
use crate::kernel::{AlgebraicValueType, int32};

#[test]
fn named_resource_bindings_preserve_symbolic_fields_and_recheck_expansion() {
    let source = r#"verifying "identity.c";
        spec enum Mark { Clear, Set }
        resource marked_cell() {
            field model: Mark;
            field revision: int32;
            field contents: List<int32>;
        }
        int32 identity(int32 value) {
            owns cell: marked_cell();
            ensures result == value;
            ensures cell.model == old(cell.model);
            ensures cell.revision == old(cell.revision);
            ensures cell.contents == old(cell.contents);
            ensures list_length(cell.contents) == old(list_length(cell.contents));
        } by { execute(); simp(); }
    "#;
    let sources = [(
        "identity.c",
        "int32 identity(int32 value) { return value; }",
    )];
    let verified = verify_c0_sources(source, &sources).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let expanded_source = source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&expanded_source, &sources)
        .expect("expanded resource-field proof must recheck");
    for false_claim in [
        "cell.model == Mark::Clear",
        "cell.revision == 0",
        "cell.contents == List::Nil",
    ] {
        let wrong = source.replace("cell.model == old(cell.model)", false_claim);
        assert!(
            verify_c0_sources(&wrong, &sources).is_err(),
            "an arbitrary field cannot prove {false_claim}"
        );
    }
}

#[test]
fn named_resource_bindings_are_scoped_and_have_distinct_state() {
    let header = "spec enum Mark { Clear, Set } resource marked_cell() { field model: Mark; }";
    for body in [
        "int32 f() { owns cell: marked_cell(); owns cell: marked_cell(); }",
        "int32 f(int32 cell) { owns cell: marked_cell(); }",
        "int32 f() { owns cell: marked_cell(); ensures cell.missing == 0; }",
        "int32 f() { owns cell: marked_cell(); ensures cell->model == Mark::Clear; }",
        "abstract resource credit(); int32 f() { owns cell: credit(); }",
    ] {
        assert!(
            parser::parse(&format!("{header} {body}")).is_err(),
            "must reject {body}"
        );
    }
    let out_of_scope = format!(
        r#"verifying "g.c"; {header}
        extern int32 f() {{ owns cell: marked_cell(); }}
        int32 g() {{ ensures cell.model == Mark::Clear; }} by {{ execute(); simp(); }}"#
    );
    assert!(verify_c0_sources(&out_of_scope, &[("g.c", "int32 g(void) { return 0; }")]).is_err());
    let source = format!(
        r#"verifying "f.c"; {header}
        int32 f() {{ owns first: marked_cell(); owns second: marked_cell();
            ensures first.model == second.model;
        }} by {{ execute(); simp(); }}"#
    );
    assert!(verify_c0_sources(&source, &[("f.c", "int32 f(void) { return 0; }")]).is_err());
    let file = parser::parse(&source).unwrap();
    let function = &file.function_blocks()[0];
    let Requirement::Resource(ResourceClause::Named { binding: first, .. }) =
        &function.requires()[0]
    else {
        panic!("missing named binding")
    };
    let Requirement::Resource(ResourceClause::Named {
        binding: second, ..
    }) = &function.requires()[1]
    else {
        panic!("missing named binding")
    };
    assert_ne!(first.identity, second.identity);
    assert_ne!(first.fields, second.fields);
    let Ensure::Resource(ResourceClause::Named {
        binding: returned, ..
    }) = function.ensures()[0].ensure()
    else {
        panic!("missing returned instance")
    };
    assert_eq!(first.identity, returned.identity);
    assert!(std::sync::Arc::ptr_eq(
        first.fields.as_ref().unwrap(),
        returned.fields.as_ref().unwrap()
    ));
}

#[test]
fn named_resource_field_metadata_is_shared_at_multiple_sizes() {
    for size in [8, 32, 128, 512] {
        let fields = (0..size)
            .map(|i| format!("field f{i}: int32;"))
            .collect::<String>();
        let claims = (0..size)
            .map(|i| format!("ensures cell.f{i} == old(cell.f{i});"))
            .collect::<String>();
        let file = parser::parse(&format!(
            "resource record() {{ {fields} }} int32 f() {{ owns cell: record(); {claims} }}"
        ))
        .unwrap();
        let function = &file.function_blocks()[0];
        let Requirement::Resource(ResourceClause::Named { binding, .. }) = &function.requires()[0]
        else {
            panic!("missing instance")
        };
        let Ensure::Resource(ResourceClause::Named {
            binding: returned, ..
        }) = function.ensures()[0].ensure()
        else {
            panic!("missing returned instance")
        };
        assert_eq!(binding.fields.as_ref().unwrap().len(), size);
        assert!(std::sync::Arc::ptr_eq(
            binding.fields.as_ref().unwrap(),
            returned.fields.as_ref().unwrap()
        ));
        assert_eq!(function.ensures().len(), size + 1);
        for (i, ensure) in function.ensures()[1..].iter().enumerate() {
            let Ensure::Proposition(ClickProposition::Comparison {
                left: ContractExpression::ResourceField(access),
                ..
            }) = ensure.ensure()
            else {
                panic!("missing projected field")
            };
            assert_eq!(access.field_index, i);
        }
    }
}

#[test]
fn named_resource_binding_does_not_expose_its_memory_body() {
    let source = r#"verifying "read.c";
        resource cell(p: int32*) { field model: List<int32>; owns p[0..1]; }
        int32 read(int32* p) {
            owns cell: cell(p);
            ensures cell.model == old(cell.model);
        } by { execute(); simp(); }
    "#;
    assert!(
        verify_c0_sources(source, &[("read.c", "int32 read(int32* p) { return *p; }")]).is_err(),
        "binding an opaque instance must not grant its unopened memory body"
    );
}

#[test]
fn named_resource_calls_reject_missing_binder_transport() {
    let source = r#"verifying "calls.c";
        resource marker() { field revision: int32; }
        extern int32 callee() { owns cell: marker(); }
        int32 caller() {
            owns cell: marker();
            ensures cell.revision == old(cell.revision);
        } by { execute(); simp(); }
    "#;
    let error = verify_c0_sources(
        source,
        &[(
            "calls.c",
            "int32 callee(void); int32 caller(void) { return callee(); }",
        )],
    )
    .unwrap_err();
    assert!(
        error.message().contains("checked binder transport"),
        "{}",
        error.message()
    );
}

#[test]
fn resource_fields_preserve_checked_types_and_do_not_lower_to_legacy_resources() {
    let file = parser::parse(
        r#"
        spec enum Mark { Clear, Set, }
        resource buffer(p: int32*) {
            field contents: List<List<int32>>;
            field mark: Mark;
            field revision: int32;
            field origin: int32*;
            owns p[0..1];
        }
        abstract resource credit();
    "#,
    )
    .unwrap();
    let buffer = &file.resource_definitions()[0];
    assert!(!buffer.is_countable());
    assert_eq!(
        buffer.fields().iter().map(|f| f.name()).collect::<Vec<_>>(),
        ["contents", "mark", "revision", "origin"]
    );
    let schema = buffer.field_schema().unwrap();
    assert!(!schema.is_countable());
    assert_eq!(schema.fields().len(), 4);
    let crate::kernel::ResourceFieldType::Algebraic(ty) = &schema.fields()[0].1 else {
        panic!("expected List schema")
    };
    assert_eq!(ty.name, "List");
    assert_eq!(
        ty.arguments,
        vec![AlgebraicValueType::Algebraic {
            name: "List".into(),
            arguments: vec![AlgebraicValueType::C(CType::Int32)],
        }]
    );
    assert_eq!(
        schema.fields()[2].1,
        crate::kernel::ResourceFieldType::C(CType::Int32)
    );
    assert_eq!(
        schema.fields()[3].1,
        crate::kernel::ResourceFieldType::C(CType::Int32Pointer)
    );
    assert!(file.resource_definitions()[1].is_countable());
    let lowered = composite_resource_definitions(
        &ResourceEnvironment::new(file.resource_definitions()),
        &PredicateEnvironment::new(&[]),
        &ClickFunctionEnvironment::new(&[]),
    )
    .unwrap();
    assert!(
        lowered.is_empty(),
        "field metadata must never be erased into a legacy composite"
    );
}

#[test]
fn resource_fields_reject_counting_and_unimplemented_instance_operations() {
    let declaration = "resource cell(p: int32*) { field model: List<int32>; owns p[0..1]; }";
    for expression in ["count(cell(p))", "List::Cons(count(cell(p)), List::Nil)"] {
        let result_type = if expression.starts_with("List") {
            "List<int32>"
        } else {
            "int32"
        };
        let source = format!(
            "function population(p: int32*) -> {result_type} {{ {expression} }} {declaration}"
        );
        assert_eq!(
            parser::parse(&source).unwrap_err().message(),
            "resource `cell` has fields and is not countable"
        );
    }
    for clause in [
        "requires count(cell(p)) == 1;",
        "requires count(cell(_)) == 1;",
        "consumes 2 of cell(p);",
        "produces 1 of cell(p);",
    ] {
        let source = format!("{declaration} int32 f(int32* p) {{ {clause} }}");
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(
            error.message(),
            "resource `cell` has fields and is not countable",
            "{clause}"
        );
    }
    let nested = format!(
        "{declaration} abstract resource credit(n: int32); int32 f(int32* p) {{ consumes credit(count(cell(p))); }}"
    );
    assert_eq!(
        parser::parse(&nested).unwrap_err().message(),
        "resource `cell` has fields and is not countable"
    );
    for tactic in [
        "apply(law(count(cell(p))));",
        "witness(x = count(cell(p)));",
    ]
    .into_iter()
    {
        let source =
            format!("{declaration} int32 f(int32* p) {{ ensures result == 0 by {{ {tactic} }} }}");
        assert_eq!(
            parser::parse(&source).unwrap_err().message(),
            "resource `cell` has fields and is not countable"
        );
    }
    for clause in [
        "consumes cell(p);",
        "produces cell(p);",
        "owns cell(p);",
        "views cell(p);",
    ] {
        let source = format!("{declaration} int32 f(int32* p) {{ {clause} }}");
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(
            error.message(),
            "resource `cell` has fields; bind it with `owns name: cell(...);`",
            "{clause}"
        );
    }
    for tactic in ["fold", "unfold", "observe", "construct"] {
        let source = format!(
            "{declaration} int32 f(int32* p) {{ ensures result == 0 by {{ {tactic}(cell(p)); }} }}"
        );
        let error = parser::parse(&source).unwrap_err();
        assert_eq!(
            error.message(),
            "resource `cell` has fields; bind it with `owns name: cell(...);`",
            "{tactic}"
        );
    }
}

#[test]
fn resource_fields_reject_invalid_declarations() {
    for (body, expected) in [
        (
            "field x: int32; field x: int32;",
            "duplicates a field or parameter name",
        ),
        ("field p: int32;", "duplicates a field or parameter name"),
        ("field x: Missing;", "unknown algebraic datatype"),
        ("field x: List;", "expects 1 type argument"),
        ("field x: List<Missing>;", "unknown algebraic datatype"),
        (
            "field x: void;",
            "requires an unqualified scalar, pointer, or algebraic Click type",
        ),
        (
            "owns p[0..1]; field x: int32;",
            "resource fields must be declared before body clauses",
        ),
        (
            "if p != 0 { field x: int32; }",
            "resource fields must be declared before body clauses",
        ),
        ("field x: int32; fact x == 0;", "x"),
    ] {
        let source = format!("resource cell(p: int32*) {{ {body} }}");
        let error = parser::parse(&source).unwrap_err();
        assert!(
            error.message().contains(expected),
            "{body}: {}",
            error.message()
        );
    }
}

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
