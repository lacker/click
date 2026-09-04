# Function-like macros reject more than three parameters

The bounded function-like macro subset accepts at most three unique named
parameters.

```c filename=main.c
#define PICK(first, second, third, fourth) first

int32 run() {
    return PICK(1, 2, 3, 4);
}
```

```click
verifying "main.c";

int32 run() {
    ensures result == 1;
}
```

```expect
fail: function-like macros currently support at most three identifier parameters
```
