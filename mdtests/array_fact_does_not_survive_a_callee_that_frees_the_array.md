# epoch attack 8: the callee releases the array, and the caller allocates again

A call's checked write set is not the only thing a call does. When a contract
retires an allocation the caller held, the caller's own memory goes through
`free_heap_block`, which records a release edge naming that allocation — so a
whole-array fact meets the release whatever the write set said. Freeing is not a
way to smuggle a write past the write set: `free` needs `owns a[0..n]` as well as
the allocation authority, so the released range is in the checked write set too,
and both barriers stand independently.

The `malloc` afterwards is the second half of the attack. A declaration, an
unresolved request and a fresh allocation are all steps a whole-array fact
crosses now, and the walk does cross all three here — and still stops at the
release, naming it. A new object cannot re-animate a fact about a released one,
and it is never even the same object: a freed heap identity stays in
`deallocated_allocations`, which `heap_identity_in_use` consults before handing
out a fresh one.

```c filename=array_fact_does_not_survive_a_callee_that_frees_the_array.c
void discard(int32 a[], int32 n) {
    free(a);
}

int32 caller(int32 a[], int32 n) {
    int32* fresh;
    discard(a, n);
    fresh = malloc(4);
    if (fresh == 0) {
        return 0;
    }
    free(fresh);
    return 0;
}
```

```click
resource allocated_int32s(data: int32*, count: int32) {
    contains allocation(data, count * 4);
    owns data[0..count];
    fact data != 0;
}

verifying "array_fact_does_not_survive_a_callee_that_frees_the_array.c";

function icount(p: int32[], lo: int32, hi: int32) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(p[k]) })
}

void discard(int32 a[], int32 n) {
    requires 1 <= n;
    requires n <= 536870911;
    consumes allocated_int32s(a, n);
} by {
    unfold(allocated_int32s(a, n));
    execute();
    simp();
}

int32 caller(int32 a[], int32 n) {
    requires 1 <= n;
    requires n <= 536870911;
    consumes allocated_int32s(a, n);
} by {
    unfold(allocated_int32s(a, n));
    have 0 <= 0 by { simp(); }
    have icount(a, 0, 0) == 0 by {
        unfold(icount(a, 0, 0)) using { 0 <= 0; }
        normalize();
    }
    fold(allocated_int32s(a, n));
    step();
    step();
    step();
    branch {
        then {
            execute();
            simp();
        }
        else {
        }
    }
    have icount(a, 0, 0) == 0 by { simp(); }
    execute();
    simp();
}
```

```expect
fail: a fact about `a` as a whole does not carry across the release of `a`. Only a step the kernel proves leaves the whole object alone carries one, and a stated `separate(...)` is not read here.
```
