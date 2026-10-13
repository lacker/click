# Freshness misses Integer arguments of C-valued and algebraic applications

Soundness: soundness-adjacent. No false acceptance is known. The kernel's
fresh-identity reservation skips identities held only inside an Integer
argument of a C-valued or algebraic pure-function application. A fresh
execution can then hand out an identity the statement already holds. Today
nothing reaches this from source: lowering allocates quantifier and binder
identities at `2_000_000` and above, outside the execution band
`[1_000_000, 2_000_000)`. So freshness holds only because the surface happens
to stay out of that band, not because the kernel checks it.

## Violated invariant

A `KernelVariableGenerator` built from the identities that a state, statement,
interface or assumption set mentions must never hand out one of them. The
spec free-variable collector in `src/kernel/reasoning/variable_collection.rs`
feeds that reservation. It visits every argument of an Integer application
(`SpecIntegerExpression::PureFunctionApplication`). For a machine application
(`SpecExpression::PureFunctionApplication`) or an algebraic one
(`SpecAlgebraicExpressionNode::PureFunctionApplication`), it skips
`SpecPureFunctionArgument::Integer`. The skip came in with #250 and has no
stated reason. The bound-identity collector in the same file visits these
arguments.

## Reproduction

Reproduced on master `4493da4`, as a kernel test in
`src/kernel/tests/execution_tests.rs`:

```rust
#[test]
fn statement_reservations_cover_integer_arguments_of_machine_applications() {
    let held = Variable(ExecutionBudget::KERNEL_VARIABLE_BASE);
    let call = SpecExpression::PureFunctionApplication {
        name: "f".into(),
        arguments: vec![SpecPureFunctionArgument::Integer(SpecIntegerExpression::Term(
            IntegerTerm::var(held),
        ))],
        result_type: CType::Int32,
    };
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: call,
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            None,
            None,
        )],
        c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
    );
    let mut reserved = BTreeSet::new();
    crate::kernel::reasoning::collect_c_statement_bitvector_variables(&statement, &mut reserved);
    let mut budget = ExecutionBudget::for_new_execution();
    let mut variables = KernelVariableGenerator::fresh_for_execution(reserved);
    assert_ne!(variables.next_in(&mut budget).unwrap(), held);
}
```

The reserved set is empty, and the first fresh identity is
`Variable(1000000)`, which the statement already holds. If `f` is replaced by
an Integer application, `IntegerToMachine(g(…))`, the identity is reserved
and the stream starts at `Variable(1000001)`. This is the same path
`statement_kernel_variables` in `src/kernel/api.rs` uses for a new execution.

## Acceptance criteria

- The free-variable collector visits Integer arguments of machine and
  algebraic applications as it does Integer applications.
- The test above passes, along with a variant that uses an algebraic
  application.
