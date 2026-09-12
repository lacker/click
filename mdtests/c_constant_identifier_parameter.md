# Declared C identifiers retain their value

A parameter named `INFINITY` is an ordinary integer identifier when no macro
replaces it. The comparison returns zero when the input is nonpositive.

```c filename=positive.c
int positive(int INFINITY) { return INFINITY > 0; }
```

```click
verifying "positive.c";
int positive(int INFINITY) {
    requires INFINITY <= 0;
    ensures result == 0;
}
```

```expect
pass
```
