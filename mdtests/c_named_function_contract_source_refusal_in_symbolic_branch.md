# Derivable source-backed call in a symbolic branch retains its Have

The callback's non-strict lower bound follows from the strict symbolic branch
guard. Smart execution records that source-backed disjunctive obligation as a
branch-local Have before the callback step.

```c filename=source_refusal_branch.c
int32 apply(int32 (*callback)(int32), int32 value) {
    int32 result;
    if (value > 0) {
        result = callback(value);
    } else {
        result = value;
    }
    return result;
}
```

```click
verifying "source_refusal_branch.c";

contract int32 Positive(int32 value) {
    requires value >= 0 or value == -1;
    requires value >= 0 or value == -1;
    ensures result == value;
}

int32 apply(int32 (*callback)(int32), int32 value) {
    requires Positive(callback);
    ensures result == value;
} by { execute(); simp(); }
```

```expect
pass
```
