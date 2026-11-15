# Integer theorem arguments retain observation states

```c filename=integer_observed_arguments_states.c
void decrement(int32 a) {
    a = a - 1;
}
```

```click
verifying "integer_observed_arguments_states.c";

theorem observed_identity(n: Integer) {
    requires n == 10;
    ensures n <= 10 by { solve() using { n == 10; }; }
}

void decrement(int32 a) {
    requires a == 10;
    requires to_integer(a) == 10;
    ensures 0 == 0;
} by {
    step();
    have old(to_integer(a)) <= 10 by {
        apply(observed_identity(old(to_integer(a)))) using { old(to_integer(a)) == 10; };
    }
    have at(region(0).entry, to_integer(a)) <= 10 by {
        apply(observed_identity(at(region(0).entry, to_integer(a)))) using { at(region(0).entry, to_integer(a)) == 10; };
    }
}
```

```expect
pass
```
