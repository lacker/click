# Adjacent C string literals concatenate into one stable object

C concatenates adjacent basic string literals, including when a comment
separates them. The result is lowered as one read-only byte array with one
terminating NUL.

```c filename=concatenated_string_literals.c
uint8* concatenated_string() {
    return "hello, " /* phase-six concatenation */ "world";
}
```

```click
verifying "concatenated_string_literals.c";

uint8* concatenated_string() {
    ensures readable: loadable(result[0..12]);
    ensures comma: result[5] == ',';
    ensures space: result[6] == ' ';
    ensures last: result[11] == 'd';
    ensures terminator: result[12] == '\0';
} by {
    execute();
    simp();
}
```

```expect
pass
```
