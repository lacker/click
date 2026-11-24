use super::*;

/// The tokens `looks_like_algebraic_constructor` examines while `source`
/// parses, without the standard library.
fn constructor_lookahead_tokens(source: &str) -> usize {
    CONSTRUCTOR_LOOKAHEAD_TOKENS.with(|count| count.set(0));
    parse_file_items(source).unwrap_or_else(|error| panic!("{source}: {}", error.message()));
    CONSTRUCTOR_LOOKAHEAD_TOKENS.with(std::cell::Cell::get)
}

/// Each sample doubles the input size.
fn assert_linear(samples: &[usize]) {
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0].saturating_mul(2).saturating_add(16),
            "{samples:?}"
        );
    }
}

#[test]
fn comparison_lookahead_stops_at_its_proposition() {
    // Each `x < y` once scanned to the end of the file for a `>` followed by
    // `::`, so a file of comparisons parsed in quadratic time. A conjunction
    // stays under the parser's 512-operator nesting limit.
    let statements = [32, 64, 128, 256].map(|size| {
        let mut source = String::from("theorem many(x: Integer, y: Integer) {\n");
        for _ in 0..size {
            source.push_str("    requires x < y;\n");
        }
        source.push_str("    ensures x < y by { close(); }\n}\n");
        constructor_lookahead_tokens(&source)
    });
    assert_linear(&statements);
    let conjuncts = [32, 64, 128, 256].map(|size| {
        let chain = vec!["x < y"; size].join(" and ");
        let source = format!(
            "theorem chain(x: Integer, y: Integer) {{\n    requires {chain};\n    ensures x < y by {{ close(); }}\n}}\n"
        );
        constructor_lookahead_tokens(&source)
    });
    assert_linear(&conjuncts);
}

#[test]
fn literal_reference_parsing_shares_the_source_index_as_other_literals_grow() {
    let mut samples = Vec::new();
    for count in [1, 16, 256] {
        let mut layouts = ProgramLayouts::default();
        for ordinal in 0..count {
            let id = crate::kernel::StringLiteralId::new("f", ordinal);
            let pointer = crate::kernel::SymbolicMemory::string_literal_pointer(&id, b"x\0");
            std::sync::Arc::make_mut(&mut layouts.string_literal_values).insert(
                id,
                ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer),
            );
        }
        std::sync::Arc::make_mut(&mut layouts.string_literal_owners)
            .insert("f".into(), BTreeSet::from([None]));
        let index = layouts.string_literal_values.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut parser =
                Parser::with_program_layouts("f.string_literal(0)", layouts, None).unwrap();
            assert!(std::sync::Arc::ptr_eq(
                &index,
                &parser.string_literal_values
            ));
            parser.parse_contract_expression().unwrap()
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn compound_literal_selector_uses_the_declaration_index() {
    let work = [1, 16, 256].map(|count| {
        let owner = crate::kernel::LocalFunctionId::new(None, "f".into());
        let mut layouts = ProgramLayouts::default();
        let bindings = std::sync::Arc::make_mut(&mut layouts.local_bindings);
        bindings.owners.insert("f".into(), BTreeSet::from([None]));
        for ordinal in 0..count {
            bindings.declarations.insert(
                crate::kernel::LocalBindingId::compound_literal(owner.clone(), ordinal),
                SourceBindingInfo {
                    struct_name: None,
                    aggregate: true,
                    array_shape: None,
                },
            );
        }
        let index = layouts.local_bindings.clone();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut parser =
                Parser::with_program_layouts("f.compound_literal(0)", layouts, None).unwrap();
            assert!(std::sync::Arc::ptr_eq(&index, &parser.local_bindings));
            parser.parse_contract_expression().unwrap()
        });
        work
    });
    assert!(
        work.iter().all(|sample| *sample <= work[0] + 16),
        "{work:?}"
    );
}

#[test]
fn static_declaration_preparation_is_linear_and_selector_lookup_is_indexed() {
    for size in [1usize, 16, 256] {
        let mut source = String::new();
        for i in 0..size {
            source.push_str(&format!("static int32 global_{i} = {i};\n"));
        }
        for i in 0..size {
            source.push_str(&format!(
                "int32 function_{i}(void) {{ static int32 local = {i}; return local; }}\n"
            ));
        }
        let unit = syntax::parse_translation_unit_for_source(
            &source,
            "statics.c",
            &crate::languages::c::source::ExpandedLineMap::empty(),
        )
        .unwrap();
        let (layouts, preparation) = crate::instrumentation::measure_deterministic_work(|| {
            let mut layouts = ProgramLayouts::default();
            layouts.register_file_static_bindings(&unit);
            for function in &unit.functions {
                layouts.register_local_bindings(function);
            }
            layouts
        });
        assert!(
            preparation >= 2 * size && preparation <= 6 * size + 8,
            "{size}: {preparation}"
        );
        let (expression, lookup) = crate::instrumentation::measure_deterministic_work(|| {
            let mut parser = Parser::new("\"statics.c\"::static(0)").unwrap();
            parser.local_bindings = layouts.local_bindings.clone();
            parser.parse_contract_expression().unwrap()
        });
        let ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Static(id),
        )) = expression
        else {
            panic!("static selector");
        };
        assert_eq!(id.spelling(), "global_0");
        assert_eq!(lookup, 9, "selector work changed at size {size}");
    }
}

/// Parenthesized field expressions recover nominal types from the selected
/// path. Record width and unrelated declarations do not enter that query.
#[test]
fn embedded_field_identity_uses_only_its_explicit_path() {
    use crate::languages::interface::RecordLayout;
    fn fixture(depth: usize, unrelated: usize) -> (Parser, ContractExpression) {
        let leaf = RecordLayout::from_explicit_fields(
            vec![("data".into(), InterfaceType::Int32Pointer, 0, 8)],
            8,
            8,
        )
        .unwrap();
        let mut layouts = BTreeMap::from([("Leaf".to_string(), leaf.clone())]);
        let mut previous = "Leaf".to_string();
        let mut bytes = 8;
        for level in 0..depth {
            let name = format!("Level{level}");
            let mut fields = vec![(
                "inner".into(),
                InterfaceType::Int32,
                Some(previous),
                0,
                bytes,
            )];
            for index in 0..unrelated {
                fields.push((
                    format!("unrelated{index}"),
                    InterfaceType::Int32,
                    None,
                    bytes + index as u32 * 4,
                    4,
                ));
            }
            bytes = (bytes + unrelated as u32 * 4).div_ceil(8) * 8;
            let layout =
                RecordLayout::from_explicit_fields_with_structs(fields, bytes, 8, &layouts)
                    .unwrap();
            layouts.insert(name.clone(), layout);
            previous = name;
        }
        for index in 0..unrelated {
            layouts.insert(format!("Unrelated{index}"), leaf.clone());
        }
        let mut parser = Parser::new_with_layouts("", layouts, BTreeMap::new()).unwrap();
        parser.names.struct_params.insert("object".into(), previous);
        let mut expression = ContractExpression::Binding("object".into());
        for _ in 0..depth {
            expression = ContractExpression::Field {
                pointee_struct: None,
                base: Box::new(expression),
                field: "inner".into(),
                lowered: ProgramExpression::Value(ProgramValue::Void),
                offset_bytes: crate::kernel::LayoutOffset::Bytes(0),
            };
        }
        (parser, expression)
    }
    let mut fixed = Vec::new();
    for unrelated in [0, 16, 64, 256] {
        let (parser, expression) = fixture(2, unrelated);
        let (identity, work) = crate::instrumentation::measure_deterministic_work(|| {
            parser.contract_expression_struct_name(&expression)
        });
        assert_eq!(identity.as_deref(), Some("Leaf"));
        fixed.push(work);
        let layout = parser.struct_layouts.get("Level1").unwrap();
        let (path, lookup) = crate::instrumentation::measure_deterministic_work(|| {
            layout.embedded_struct_field(0, "Level0")
        });
        assert_eq!(path.unwrap(), "inner");
        assert_eq!(lookup, 1, "embedded receiver lookup at width {unrelated}");
        assert!(layout.embedded_struct_field(8, "Level0").is_none());
        assert!(layout.embedded_struct_field(0, "Unrelated0").is_none());
    }
    assert!(
        fixed[0] > 0 && fixed.iter().all(|work| *work == fixed[0]),
        "unrelated input: {fixed:?}"
    );
    for depth in [1, 4, 16, 64] {
        let (parser, expression) = fixture(depth, 0);
        let (identity, work) = crate::instrumentation::measure_deterministic_work(|| {
            parser.contract_expression_struct_name(&expression)
        });
        assert_eq!(identity.as_deref(), Some("Leaf"));
        let layout = parser
            .struct_layouts
            .get(&format!("Level{}", depth - 1))
            .unwrap();
        let (_, lookup) = crate::instrumentation::measure_deterministic_work(|| {
            let mut layout = layout;
            for level in (0..depth).rev() {
                let target = if level == 0 {
                    "Leaf".to_owned()
                } else {
                    format!("Level{}", level - 1)
                };
                assert_eq!(layout.embedded_struct_field(0, &target), Some("inner"));
                layout = parser.struct_layouts.get(&target).unwrap();
            }
        });
        assert_eq!(lookup, depth, "embedded receiver path at depth {depth}");
        assert!(
            work >= depth && work <= 8 * (depth + 1),
            "depth {depth}: {work}"
        );
    }
}
