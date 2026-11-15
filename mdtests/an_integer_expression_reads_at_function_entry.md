# An Integer expression reads at function entry

`at(function.entry, e)` is `old(e)` for an Integer `e`, as it is for a C
value, and a state of an unsuffixed literal is the literal, so it
compares with an Integer as the literal does. Each `have` below is the
same claim about `x` at entry.

```c filename=an_integer_expression_reads_at_function_entry.c
int identity(int x) { return x; }
```

```click
verifying "an_integer_expression_reads_at_function_entry.c";
int32 identity(int32 x) {
    requires to_integer(x) == 0;
    ensures to_integer(result) == 0;
} by {
    have at(function.entry, to_integer(x)) == 0;
    have at(function.entry, to_integer(x)) == at(function.entry, 0);
    have old(to_integer(x)) == old(0);
}
```

```expect
pass
```
