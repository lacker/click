# A C parameter named `result` keeps its entry value

```c filename=bump.c
int32 bump(int32 result) {
    return result + 1;
}
```

```click
verifying "bump.c";

int32 bump(int32 result) {
    requires 0 <= c(result) and c(result) <= 100;
    ensures result == at(function.entry, c(result)) + 1;
}
```

```expect
pass
```
