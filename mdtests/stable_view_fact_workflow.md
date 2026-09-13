# A current view can support a resource fact in a proof workflow

The resource fact reads the cell covered by its current view. Opening the
resource makes that fact available to the ordinary reader proof.

```c filename=stable_view_fact_workflow.c
int32 stable_view_fact_reader(int32 p[]) {
    return p[0];
}
```

```click
resource stable_cell(p: int32*) {
    views p[0..1];
    fact p[0] == 0;
}

verifying "stable_view_fact_workflow.c";

int32 stable_view_fact_reader(int32 p[]) {
    views stable_cell(p);
    ensures result == 0;
} by {
    open(stable_cell(p)) {
        execute();
        simp();
    }
}
```

```expect
pass
```
