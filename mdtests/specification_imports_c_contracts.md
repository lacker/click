# Import C contracts and tactics

C contracts and tactics use the same import syntax. The helper library is
verified separately; its contracts are assumptions while checking this caller.

```c filename=specification_imports_helpers.c
int imported_helper(int x) { return x; }
int imported_caller(int x) { return imported_helper(x); }
void imported_keep(int *p) {}
void imported_resource_caller(int *p) { imported_keep(p); }
```

```click
import "specification_imports_helpers.click";
verifying "specification_imports_helpers.c";

theorem imported_contract_is_available() {
    ensures ImportedIdentity(&imported_helper) by { unfold(ImportedIdentity); simp(); }
}

int32 imported_caller(int32 x) {
    ensures result == x;
} by {
    retain_equal(x, x);
    execute();
    simp();
}
void imported_resource_caller(int32* p) {
    consumes input: imported_cell(p);
    produces output: imported_cell(p);
    ensures output.value == old(input.value);
} by {
    let { after: middle } = step(imported_keep(p), { before: input });
    let { after: output } = imported_rename(p, { before: middle });
    execute();
    simp();
}
```

```expect
pass
```
