# Indexed unfold must run before function exit

indexed `unfold` moves an element at the execution frontier. After `step_until(function.exit)` reaches the exit there is none, and the refusal says so instead of reporting an unsupported proof shape.

```c filename=indexed_unfold_after_function_exit_is_refused.c
void f(int *data, int *occupied, int capacity, int index) { }
```

```click
resource cells(data: int32*, occupied: int32*, capacity: int32) {
    owns occupied[0..capacity];
    forall (k: int32) where 0 <= k and k < capacity {
        if occupied[k] == 0 {
            owns data[k..k + 1];
        }
    }
}

verifying "indexed_unfold_after_function_exit_is_refused.c";

void f(int32* data, int32* occupied, int32 capacity, int32 index) {
    owns cells(data, occupied, capacity);
    requires 0 <= index; requires index < capacity; requires occupied[index] == 0;
} by {
    unfold(cells(data, occupied, capacity));
    step_until(function.exit);
    unfold(cells(data, occupied, capacity)[index]);
    fold(cells(data, occupied, capacity)[index]);
    fold(cells(data, occupied, capacity));
    close();
}
```

```expect
fail: `unfold(cells(data, occupied, capacity)[index])` must run before execution reaches function exit
```
