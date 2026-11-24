# A callback may not require ownership its named contract does not supply

The concrete callback's body writes only the first cell, but its published
contract requires ownership of two.  A named contract transferring only the
first cell cannot satisfy that extra requirement.

```c filename=extra_callback_resource_requirement.c
void needs_two_cells(int32* state) {
    state[0] += 1;
}

void apply_step(void (*step)(int32*), int32* cells) {
    step(cells);
}

void extra_resource_caller(int32* cells) {
    apply_step(&needs_two_cells, cells);
}
```

```click
verifying "extra_callback_resource_requirement.c";

contract void Progress(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..1];
    ensures old(cells[0]) < cells[0];
}

void needs_two_cells(int32* state) {
    requires state[0] < 100;
    views state[1..2];
    owns state[0..1];
    ensures state[0] == old(state[0]) + 1;
}

void apply_step(void (*step)(int32*), int32* cells) {
    requires Progress(step);
    requires cells[0] < 100;
    owns cells[0..1];
    ensures old(cells[0]) < cells[0];
}

theorem proposed_needs_two_cells_contract() {
    ensures Progress(&needs_two_cells) by {
        unfold(Progress(&needs_two_cells));
        close();
    }
}

void extra_resource_caller(int32* cells) {
    requires cells[0] < 100;
    owns cells[0..1];
    ensures old(cells[0]) < cells[0];
} by {
    apply(proposed_needs_two_cells_contract());
}
```

```expect
fail: contract-refinement proof does not establish `Progress(&needs_two_cells)`
```
