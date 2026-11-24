# Execution theorem uses an imported tactic

The imported procedure runs no C code and preserves the owned cell's value.
Its signature must be available in ordinary verification and theorem expansion;
its body is checked separately in the helper sidecar.

```c filename=caller.c
int32 zero(int32* p) { return 0; }
```

```click
verifying "caller.c";
import "execution_theorem_imported_tactic_helpers.click";
int32 zero(int32* p) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.value == old(before.value);
    ensures result == 0;
} by {
    unfold(before);
    step_until(function.exit);
    let after = fold(cell(p), { value: *p });
    close();
}
contract int32 Keep(int32* p) {
    consumes before: cell(p);
    produces after: cell(p);
    ensures after.value == old(before.value);
    ensures result == 0;
}
theorem zero_contract() executes zero(int32* p) {
    ensures Keep(&zero) as { before: input, after: output } by {
        let { after: middle } = rename_cell(p, { before: input });
        let { after: output } = step(zero, { before: middle });
        close();
    }
}
```

```expect
pass
```
