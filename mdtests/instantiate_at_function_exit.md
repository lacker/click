# Instantiate available universals at function exit

The first instantiation adds a fact while the ownership claim is open.
The second adds exactly the current existential goal. The proof can still
choose an explicit witness before closing that claim.

```c filename=instantiate_at_exit.c
int32 at_exit(int32* p, int32 n) { return n; }
```

```click
verifying "instantiate_at_exit.c";

function f(k: int32) -> int32 { k }

int32 at_exit(int32* p, int32 n) {
    requires forall (k: int32) { f(k) == k };
    requires forall (k: int32) { exists (j: int32) { j == k } };
    owns *p;
    ensures f(result) == result;
    ensures exists (j: int32) { j == result };
} by {
    step_until(function.exit);
    instantiate(forall (k: int32) { f(k) == k }, result);
    close();
    close();
    instantiate(forall (k: int32) { exists (j: int32) { j == k } }, result);
    witness(result);
    close();
}
```

```expect
pass
```
