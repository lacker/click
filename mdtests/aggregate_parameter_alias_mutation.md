# An alias cannot expose a changed private parameter field to callers

```c filename=parameter_alias_mutation.c
struct packet { int32 value; };
int32 change(struct packet input) {
    int32* alias = &input.value;
    *alias = 5;
    return 0;
}
```

```click
verifying "parameter_alias_mutation.c";
int32 change(struct packet input) {
    ensures input.value == 5;
} by { execute(); simp(); }
```

```expect
fail: did not retain a complete proof
```
