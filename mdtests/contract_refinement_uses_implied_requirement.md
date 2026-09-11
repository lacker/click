# Contract refinement eliminates an implication among the target's requirements

Forming a named contract for a concrete function assumes the contract's
requirements and then checks the function's own. When one requirement is an
implication whose antecedent is another requirement, the consequent is
available to the refinement: `assume_contract_proposition` discharges the
antecedent while assuming, so `n == 7` reaches the check even though only
`flag == 1` and `flag == 1 implies n == 7` were written.

Package 10(b) of `issues/simplify-kernel.md` restricted that discharge to the
exact routes — the exact fact index, the frozen condition checker on a bare
condition, and the frozen atomic memory/resource checkers. The antecedent here
is exactly the preceding requirement, so the exact index answers it. This is
the fixture that reaches the site: the census found no other.

```c filename=implied_requirement.c
void use_seven(int32 flag, int32 n) {
}

void invoke_guarded(void (*callback)(int32, int32), int32 flag, int32 n) {
    callback(flag, n);
}

void guarded_caller(int32 flag, int32 n) {
    invoke_guarded(&use_seven, flag, n);
}
```

```click
verifying "implied_requirement.c";

contract void Guarded(int32 flag, int32 n) {
    requires flag == 1;
    requires flag == 1 implies n == 7;
    ensures 0 <= n;
}

void use_seven(int32 flag, int32 n) {
    requires n == 7;
    ensures 0 <= n;
} by auto;

void invoke_guarded(void (*callback)(int32, int32), int32 flag, int32 n) {
    requires Guarded(callback);
    requires flag == 1;
    requires n == 7;
    ensures 0 <= n;
} by auto;

void guarded_caller(int32 flag, int32 n) {
    requires flag == 1;
    requires n == 7;
    ensures 0 <= n;
} by auto;
```

```expect
pass
```
