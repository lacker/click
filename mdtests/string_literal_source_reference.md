# Literal objects are named by their function and occurrence

```c filename=literal_reference.c
const char* text() { return "hello"; }
int first() { const char* p = text(); return p[0]; }
const char* own() { text(); return "own"; }
```

```click
verifying "literal_reference.c";
const char* text() {
    produces result[0..6];
    ensures result == text.string_literal(0);
    ensures result[0] == 104;
}
const char* own() {
    ensures result == own.string_literal(0);
}
int32 first() {
    ensures result == 104;
} by {
    step_until(function.exit);
    have "literal_reference.c"::text.string_literal(0)[0] == 104 by { close(); }
    close();
}
```

```expect
pass
```
