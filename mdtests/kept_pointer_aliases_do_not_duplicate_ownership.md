# Stated aliases do not grant duplicate ownership

```c filename=alias_overlap.c
struct box { int32 v; };
void caller(struct box* b, struct box* q0, struct box* q1, struct box* q2, struct box* q3, struct box* q4, struct box* q5, struct box* q6, struct box* q7) { return; }
```

```click
verifying "alias_overlap.c";
void caller(struct box* b, struct box* q0, struct box* q1, struct box* q2, struct box* q3, struct box* q4, struct box* q5, struct box* q6, struct box* q7) {
    owns *b;
    owns *q0;
    requires q0 == b;
    requires q1 == b;
    requires q2 == b;
    requires q3 == b;
    requires q4 == b;
    requires q5 == b;
    requires q6 == b;
    requires q7 == b;
} by { execute(); simp(); }
```

```expect
fail: overlap
```
