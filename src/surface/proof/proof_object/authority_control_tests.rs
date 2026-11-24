use super::*;

// Regression for the population nightly failure fixed by a96180944. Its count
// invariant is essential: removing it makes the faulty recorder accept this
// proof. The full source completes normally; this test stops at the failed open.
// The original shared_heap_population_certification.md remains in the nightly
// proof corpus and repository expansion audit, which checks all 19 smart sites.
const CONTROL_SOURCE: &str = r#"spec enum Link { Present(int32*) }
resource slot(p: int32**) {
    field link: Link;
    match link {
        Link::Present(obj) => {
            owns *p;
            fact defined(*p);
            fact *p == obj;
            fact obj != 0;
        },
    }
}
authorized resource reference(obj: int32*) {}
resource control(obj: int32*) {
    owns *obj;
    owns authority(reference(obj));
    fact defined(*obj);
    fact *obj == count(reference(obj));
}
verifying "f.c";
int32 read_ref(int32** p) {
    owns saved: slot(p);
    owns control(*p);
    ensures result == old(**p);
} by {
    match saved.link {
        Link::Present(linked) => {
            unfold(saved);
            have old(*p) == linked by { close(); }
            with(control(*p)) { step_until(function.exit); }
            let saved = fold(slot(p), { link: Link::Present(linked) });
            close();
        },
    }
}
"#;
const C_SOURCE: &str = "int32 read_ref(int32** p) { int32* obj = *p; return *obj; }";

#[test]
fn opening_control_retains_loaded_pointer_facts() {
    let _session = crate::kernel::VerificationSession::enter();
    let file = crate::surface::verification::parse_click_file_with_c_sources(
        CONTROL_SOURCE,
        &[("f.c", C_SOURCE)],
    )
    .unwrap();
    let parsed = syntax::parse_function(C_SOURCE).unwrap();
    let block = &file.function_blocks()[0];
    let predicates = PredicateEnvironment::new(file.predicate_definitions());
    let functions = ClickFunctionEnvironment::with_algebraic_types(
        file.click_function_definitions(),
        file.algebraic_type_definitions(),
    );
    let theorems = TheoremEnvironment::new(file.theorem_definitions());
    let resources = ResourceEnvironment::new(file.resource_definitions());
    let specs = SpecDefinitions::new(&predicates, &functions);
    let function = parsed
        .to_kernel_function()
        .with_composite_resource_definitions(
            crate::surface::verification::composite_resource_definitions(&resources, specs)
                .unwrap(),
        );
    let (state, arguments, facts, surfaces) =
        initial_claim_context(block, &parsed, &resources, specs, "loaded control").unwrap();
    let environment = ExecutionEnvironment::new();
    let root = Proof::for_execution_frontier(
        "loaded control",
        0,
        ExecutionProofState::at_entry(
            state,
            ExecutionFrontier::default(),
            RecordedStates::new(),
            surfaces,
            PersistentSequence::default(),
        ),
        facts,
        ExecutionProofConstants::default(),
        block,
        &function,
        &parsed,
        &arguments,
        &environment,
        &resources,
        specs,
        &theorems,
    );
    let [ProofTactic::Match(source)] = block.grouped_proof().unwrap().tactics().unwrap() else {
        panic!("the reproduction selects one model constructor");
    };
    let prepared = root.prepare_execution_match(false, 0).unwrap();
    let plan = prepared.plan_execution_match(source, |_| 1).unwrap();
    let arm = prepared.enter_execution_match_arm(&plan, 0).unwrap();
    let [
        ProofTactic::UnfoldResource(parent),
        ProofTactic::Have(have),
        ProofTactic::Open(open),
        ..,
    ] = source.arms[0].tactics.as_slice()
    else {
        panic!("the reproduction unfolds, names the alias, and opens its control");
    };
    let unfolded = arm
        .driver()
        .apply_step(ProofStep::UnfoldResource(parent.clone()))
        .unwrap();
    let named = unfolded
        .driver()
        .open_have(have.proposition.clone())
        .unwrap()
        .driver()
        .apply_step(ProofStep::Known)
        .unwrap()
        .join()
        .unwrap();
    let opened = named
        .begin_open(open.resource.clone(), 3)
        .expect("opening the control must retain its loaded-pointer facts");
    // Entry reads can already name the same pointer before the control opens.
    // Check that the scope retains the equality the proof can use.
    opened
        .body()
        .driver()
        .open_have(have.proposition.clone())
        .unwrap()
        .driver()
        .apply_step(ProofStep::Known)
        .unwrap()
        .join()
        .unwrap();
    assert!(root.certificate().steps().is_empty());
}
