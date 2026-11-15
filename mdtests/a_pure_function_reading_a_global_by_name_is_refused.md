# a pure function reading a global by name is refused

A pure function application is a term over its argument values; the only
memory it carries is the state inside an array-ref argument. A body that
read the file-scope object `counter` by name would make `read_counter(0)` one
term before and after `counter = counter + 1`, and the `requires` fact about
it would discharge the false `ensures` verbatim. Such a body is refused when
the verification starts, with the remedy: pass the value as an argument
(`mdtests/a_pure_function_takes_a_global_value_as_an_argument.md`).

```c filename=bump.c
int32 counter = 1;

int32 bump() {
    counter = counter + 1;
    return counter;
}
```

```click
verifying "bump.c";

function read_counter(x: int32) -> int32 {
    counter + x
}

int32 bump() {
    owns counter;
    requires counter == 5;
    requires read_counter(0) == 5;
    ensures counter == 6;
    ensures read_counter(0) == 5;
}
```

```expect
fail: pure function `read_counter` reads the C object `counter` by name
```
