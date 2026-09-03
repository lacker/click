# Calls in conditional-expression branches stay lazy

An expression-level call in either arm of `?:` must execute only when that arm
is selected. The lowering uses a statement-level `if` around the existing
checked call transition.

```c filename=call_in_conditional_branch.c
int32 call_in_conditional_branch(int32 condition) {
    return condition ? increment() : 0;
}
```

```c filename=increment.c
int32 increment() {
    return 1;
}
```

```click
verifying "call_in_conditional_branch.c";
verifying "increment.c";

int32 call_in_conditional_branch(int32 condition) {
    requires condition != 0;
    ensures result == 1 by auto;
}

int32 increment() {
    ensures result == 1 by auto;
}
```

```expect
pass
```
