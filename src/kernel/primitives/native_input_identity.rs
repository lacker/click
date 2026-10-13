//! Declaration-only selection of opaque input identities. No resource body
//! is opened and no object extent, cell or access authority is established.
use super::*;

type Node = (usize, usize);
type Formals<'a> = BTreeMap<&'a str, (usize, CType)>;

#[derive(Default)]
struct DefinitionEdges {
    direct: BTreeSet<usize>,
    children: BTreeMap<usize, BTreeSet<Node>>,
}

fn formals(parameters: &[CParameter]) -> Formals<'_> {
    parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            crate::instrumentation::record_deterministic_work(1);
            (parameter.name(), (index, parameter.c_type()))
        })
        .collect()
}

fn definition_index(definitions: &[CCompositeResourceDefinition], name: &str) -> Option<usize> {
    definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        })
        .ok()
}

fn composite(term: &CResourceTerm) -> Option<(&str, &[CExpression], &[CType])> {
    let mut term = term;
    while let Some(inner) = term.instance_resource() {
        crate::instrumentation::record_deterministic_work(1);
        term = inner;
    }
    match term {
        CResourceTerm::Composite {
            name,
            arguments,
            parameter_types,
            ..
        } => Some((name, arguments, parameter_types)),
        _ => None,
    }
}

fn mappings(
    source: &Formals<'_>,
    target: &[CParameter],
    arguments: &[CExpression],
    declared_types: Option<&[CType]>,
    shadowed: &BTreeSet<&str>,
) -> Vec<(usize, usize)> {
    if target.len() != arguments.len()
        || declared_types.is_some_and(|types| {
            types.len() != target.len()
                || types
                    .iter()
                    .zip(target)
                    .any(|(declared, formal)| *declared != formal.c_type())
        })
    {
        return Vec::new();
    }
    target
        .iter()
        .zip(arguments)
        .enumerate()
        .filter_map(|(target_index, (formal, argument))| {
            crate::instrumentation::record_deterministic_work(1);
            let CExpression::Variable(name) = argument else {
                return None;
            };
            if shadowed.contains(name.as_str()) {
                return None;
            }
            let &(source_index, source_type) = source.get(name.as_str())?;
            (source_type.is_object_pointer() && source_type == formal.c_type())
                .then_some((source_index, target_index))
        })
        .collect()
}

fn add_specs(
    specs: &[CResourceSpec],
    source: &Formals<'_>,
    definitions: &[CCompositeResourceDefinition],
    shadowed: &BTreeSet<&str>,
    edges: &mut DefinitionEdges,
) {
    for spec in specs {
        crate::instrumentation::record_deterministic_work(1);
        for requirement in spec.native_span_requirements() {
            crate::instrumentation::record_deterministic_work(1);
            if let CExpression::Variable(name) = &requirement.carrier
                && !shadowed.contains(name.as_str())
                && let Some(&(index, c_type)) = source.get(name.as_str())
                && c_type.pointee_type() == Some(requirement.element_type)
            {
                edges.direct.insert(index);
            }
        }
        let Some((name, arguments, types)) = composite(spec.term()) else {
            continue;
        };
        let Some(target) = definition_index(definitions, name) else {
            continue;
        };
        for (source, formal) in mappings(
            source,
            definitions[target].parameters(),
            arguments,
            Some(types),
            shadowed,
        ) {
            edges
                .children
                .entry(source)
                .or_default()
                .insert((target, formal));
        }
    }
}

fn add_children(
    children: &[CResourceChildSpec],
    source: &Formals<'_>,
    definitions: &[CCompositeResourceDefinition],
    shadowed: &BTreeSet<&str>,
    edges: &mut DefinitionEdges,
) {
    for child in children {
        crate::instrumentation::record_deterministic_work(1);
        let Some(target) = definition_index(definitions, &child.resource) else {
            continue;
        };
        for (source, formal) in mappings(
            source,
            definitions[target].parameters(),
            &child.arguments,
            None,
            shadowed,
        ) {
            edges
                .children
                .entry(source)
                .or_default()
                .insert((target, formal));
        }
    }
}

fn definition_edges(
    definition: &CCompositeResourceDefinition,
    definitions: &[CCompositeResourceDefinition],
) -> DefinitionEdges {
    let source = formals(definition.parameters());
    let unshadowed = BTreeSet::new();
    let mut edges = DefinitionEdges::default();
    add_specs(
        &definition.contains,
        &source,
        definitions,
        &unshadowed,
        &mut edges,
    );
    add_children(
        &definition.children,
        &source,
        definitions,
        &unshadowed,
        &mut edges,
    );
    for arm in definition.matched.iter().flat_map(|body| &body.arms) {
        let shadowed = arm
            .bindings
            .iter()
            .map(|name| {
                crate::instrumentation::record_deterministic_work(1);
                name.as_str()
            })
            .collect::<BTreeSet<_>>();
        add_specs(&arm.contains, &source, definitions, &shadowed, &mut edges);
        add_children(&arm.children, &source, definitions, &shadowed, &mut edges);
    }
    edges
}

impl CFunctionContractInterface {
    /// Select opaque formal identities through exactly declared same-type
    /// child mappings. Conditional bodies affect identity selection only;
    /// their guards and native promises still need ordinary admission.
    /// Definitions use the checked name-sorted vocabulary: source lowering
    /// emits declaration-map order and interfaces retain the same index.
    pub(crate) fn declared_span_identity_parameters(
        parameters: &[CParameter],
        specs: &[CResourceSpec],
        definitions: &[CCompositeResourceDefinition],
    ) -> BTreeSet<usize> {
        let mut roots = DefinitionEdges::default();
        add_specs(
            specs,
            &formals(parameters),
            definitions,
            &BTreeSet::new(),
            &mut roots,
        );
        let mut selected = roots.direct;
        let mut root_nodes = BTreeMap::<Node, BTreeSet<usize>>::new();
        for (formal, nodes) in roots.children {
            for node in nodes {
                root_nodes.entry(node).or_default().insert(formal);
            }
        }
        let mut pending = root_nodes.keys().copied().collect::<Vec<_>>();
        let mut visited = BTreeSet::new();
        let mut cached = BTreeMap::<usize, DefinitionEdges>::new();
        let mut reverse = BTreeMap::<Node, BTreeSet<Node>>::new();
        let mut needed = BTreeSet::new();
        while let Some(node @ (definition, formal)) = pending.pop() {
            if !visited.insert(node) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            let edges = cached
                .entry(definition)
                .or_insert_with(|| definition_edges(&definitions[definition], definitions));
            if edges.direct.contains(&formal) {
                needed.insert(node);
            }
            if let Some(children) = edges.children.get(&formal) {
                for child in children {
                    crate::instrumentation::record_deterministic_work(1);
                    reverse.entry(*child).or_default().insert(node);
                    pending.push(*child);
                }
            }
        }
        // Propagate from actual prefix leaves through the selected reverse
        // graph. A cycle without such a leaf establishes no requirement.
        let mut pending = needed.iter().copied().collect::<Vec<_>>();
        while let Some(node) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(formals) = root_nodes.get(&node) {
                selected.extend(formals);
            }
            if let Some(parents) = reverse.get(&node) {
                for parent in parents {
                    crate::instrumentation::record_deterministic_work(1);
                    if needed.insert(*parent) {
                        pending.push(*parent);
                    }
                }
            }
        }
        selected
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{c_function, c_int32_literal, c_parameter, c_skip, c_variable};

    fn prefix() -> CResourceSpec {
        CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))
        .with_native_span_requirements(vec![CNativeSpanRequirement {
            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
            carrier: c_variable("p"),
            element_type: CType::Int32,
            count: c_int32_literal(1),
        }])
    }

    fn head(name: &str) -> CResourceSpec {
        CResourceSpec::composite(
            CResourceAccessMode::Own,
            name.into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
        )
    }

    fn child(name: &str, argument: CExpression) -> CResourceChildSpec {
        CResourceChildSpec {
            name: "child".into(),
            resource: name.into(),
            binding: Variable(9_898_601),
            arguments: vec![argument],
            field_bindings: Vec::new(),
        }
    }

    fn definition(
        name: &str,
        specs: Vec<CResourceSpec>,
        children: Vec<CResourceChildSpec>,
    ) -> CCompositeResourceDefinition {
        CCompositeResourceDefinition::new(
            name,
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            specs,
            Vec::new(),
        )
        .with_children(children)
    }

    fn selected(definitions: &[CCompositeResourceDefinition]) -> BTreeSet<usize> {
        CFunctionContractInterface::declared_span_identity_parameters(
            &[c_parameter("p", CType::Int32Pointer)],
            &[head("A")],
            definitions,
        )
    }

    #[test]
    fn declared_child_identity_selection_terminates_cycles_and_requires_a_prefix_leaf() {
        let a = definition("A", Vec::new(), vec![child("B", c_variable("p"))]);
        let b = definition("B", Vec::new(), vec![child("A", c_variable("p"))]);
        assert!(selected(&[a.clone(), b.clone()]).is_empty());
        let b = definition("B", vec![prefix()], b.children);
        assert_eq!(selected(&[a, b]), BTreeSet::from([0]));
    }

    #[test]
    fn declared_child_identity_requires_same_type_direct_formals_and_respects_shadowing() {
        let leaf = definition("B", vec![prefix()], Vec::new());
        let offset = CExpression::PointerOffsetBytes {
            pointer: Box::new(c_variable("p")),
            bytes: 0,
        };
        let a = definition("A", Vec::new(), vec![child("B", offset)]);
        assert!(selected(&[a, leaf.clone()]).is_empty());
        let wrong_type = CCompositeResourceDefinition::new(
            "B",
            vec![c_parameter("p", CType::UInt32Pointer)],
            None,
            false,
            vec![prefix()],
            Vec::new(),
        );
        let a = definition("A", Vec::new(), vec![child("B", c_variable("p"))]);
        assert!(selected(&[a, wrong_type]).is_empty());
        let mut a = definition("A", Vec::new(), Vec::new());
        a.matched = Some(CResourceMatchBody {
            field_index: 0,
            algebraic_type: AlgebraicType::parameter("Choice".into()),
            arms: vec![CResourceMatchArm {
                variant: "Arm".into(),
                bindings: vec!["p".into()],
                binding_types: vec![AlgebraicValueType::C(CType::Int32Pointer)],
                binding_variables: vec![None],
                contains: Vec::new(),
                facts: Vec::new(),
                children: vec![child("B", c_variable("p"))],
            }],
        });
        assert!(selected(&[a, leaf]).is_empty());
    }

    #[test]
    fn declared_inactive_child_prefix_enrolls_only_an_opaque_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let a = definition("A", vec![head("B")], Vec::new());
        let mut b = definition("B", Vec::new(), Vec::new());
        b.condition = Some(SpecProposition::Comparison {
            left: SpecExpression::Value(int32(0)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        });
        // The child promises a prefix only under its false guard. Identity
        // selection sees that declaration without assuming the guarded extent.
        b.contains = vec![prefix()];
        let definitions = vec![a, b];
        assert_eq!(selected(&definitions), BTreeSet::from([0]));
        let function = c_function(
            CType::Void,
            "inactive_child",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_skip(),
        )
        .with_resource_summary(vec![head("A")], Vec::new())
        .with_composite_resource_definitions(definitions);
        let value =
            CValue::typed_pointer(Pointer::symbolic(Variable(9_898_602)), CType::Int32Pointer);
        let entry = crate::kernel::functions::independent_entry::construct(
            &function,
            &[CExpression::Value(value)],
            None,
            false,
        )
        .expect("opaque declared input recipe");
        let CExpression::Value(CValue::Pointer(pointer)) = &entry.arguments[0] else {
            panic!("pointer input");
        };
        assert!(matches!(
            pointer.designation(),
            Some(PointerDesignation::Unresolved(_))
        ));
        assert_eq!(entry.caller.memory(), &CMemory::new());
        assert!(entry.caller.memory().native_input_span(pointer).is_none());
        assert!(
            crate::kernel::eval::pointer_domains::checked_typed_pointer_span(
                &entry.caller,
                pointer,
                IntegerTerm::constant_i64(0),
                IntegerTerm::constant_i64(1),
                CType::Int32,
                &PureFactContext::new(),
            )
            .is_err()
        );
    }

    #[test]
    fn declared_child_identity_work_tracks_only_the_selected_graph() {
        let mut unrelated_work = Vec::new();
        for unrelated in [16, 128, 1024] {
            let mut definitions = vec![
                definition("A", Vec::new(), vec![child("B", c_variable("p"))]),
                definition("B", vec![prefix()], Vec::new()),
            ];
            definitions.extend(
                (0..unrelated).map(|index| {
                    definition(&format!("noise-{index:04}"), vec![prefix()], Vec::new())
                }),
            );
            let (indices, work) =
                crate::instrumentation::measure_deterministic_work(|| selected(&definitions));
            assert_eq!(indices, BTreeSet::from([0]));
            unrelated_work.push(work);
        }
        assert!(
            unrelated_work
                .iter()
                .all(|work| *work <= unrelated_work[0] + 32),
            "{unrelated_work:?}"
        );
        for size in [4, 16, 64] {
            let mut definitions = Vec::new();
            for index in 0..size {
                let name = format!("node-{index:04}");
                definitions.push(if index + 1 == size {
                    definition(&name, vec![prefix()], Vec::new())
                } else {
                    definition(
                        &name,
                        Vec::new(),
                        vec![child(&format!("node-{:04}", index + 1), c_variable("p"))],
                    )
                });
            }
            let (indices, work) = crate::instrumentation::measure_deterministic_work(|| {
                CFunctionContractInterface::declared_span_identity_parameters(
                    &[c_parameter("p", CType::Int32Pointer)],
                    &[head("node-0000")],
                    &definitions,
                )
            });
            assert_eq!(indices, BTreeSet::from([0]));
            assert!(work <= size * 32 + 64, "size={size}, work={work}");
        }
    }
}
