use click::kernel::*;

fn true_source() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(true), true)
}

#[test]
fn inconsistent_context_retains_its_false_premise() {
    let source = true_source();
    let target = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let context = PureFactContext::new().assume_proposition(target.clone());

    let theorem = prove_c_condition_fact_target_transport(&source, &target, &context)
        .expect("supplied contextual assumption gets accepted");
    let closed = Proposition::Implies(Box::new(source.clone()), Box::new(target.clone()));
    assert_ne!(theorem.proposition(), &closed);
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(target), Box::new(closed)),
    );
}

#[test]
fn consistent_context_retains_its_symbolic_premise() {
    let source = true_source();
    let target = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(777))),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    assert!(
        prove_c_condition_fact_target_transport(&source, &target, &PureFactContext::new())
            .is_none()
    );
    let context = PureFactContext::new().assume_proposition(target.clone());

    let theorem = prove_c_condition_fact_target_transport(&source, &target, &context)
        .expect("supplied contextual assumption gets accepted");
    let closed = Proposition::Implies(Box::new(source.clone()), Box::new(target.clone()));
    assert_ne!(theorem.proposition(), &closed);
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(target), Box::new(closed)),
    );
}

#[test]
fn context_free_disjoint_store_transport_stays_closed() {
    let before = CMemory::new();
    let written = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let after = before.clone().store(written, int32(7));
    let old_load = Bitvector32Term::MemoryLoad(
        click::kernel::intern_c_memory(before),
        Box::new(preserved.clone()),
    );
    let new_load =
        Bitvector32Term::MemoryLoad(click::kernel::intern_c_memory(after), Box::new(preserved));
    let source = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(old_load.clone()), Box::new(old_load.clone())),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(new_load), Box::new(old_load)),
        true,
    );

    let theorem =
        prove_c_condition_fact_target_transport(&source, &target, &PureFactContext::new())
            .expect("a structurally disjoint store needs no contextual premise");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(source), Box::new(target)),
    );
}

#[test]
fn retained_premises_ignore_unrelated_ambient_context_at_scale() {
    let source = true_source();
    let target = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(777))),
            Box::new(Bitvector32Term::Constant(0)),
        ),
        true,
    );
    let expected = Proposition::Implies(
        Box::new(target.clone()),
        Box::new(Proposition::Implies(
            Box::new(source.clone()),
            Box::new(target.clone()),
        )),
    );
    let mut samples = Vec::new();
    for size in [8, 64, 512, 4096] {
        let mut context = PureFactContext::new().assume_proposition(target.clone());
        for index in 0..size {
            context = context.assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Variable(Variable(10_000 + index)),
                true,
            ));
        }
        let (theorem, work) = click::instrumentation::measure_deterministic_work(|| {
            prove_c_condition_fact_target_transport(&source, &target, &context)
                .expect("the exact target premise is indexed")
        });
        assert_eq!(theorem.proposition(), &expected);
        samples.push((size, work));
    }
    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 8),
        "retaining one exact premise must not scan or wrap unrelated facts: {samples:?}"
    );
}
