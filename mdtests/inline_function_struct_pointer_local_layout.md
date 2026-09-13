# a `static inline` function's struct-pointer local keeps its layout

`mdtests/struct_pointer_local_has_a_layout.md` gave an automatic local of
struct-pointer type the struct name its declaration spells, so `p->word` in a
`have` resolves against the struct's layout instead of lowering to no path.
The layouts travelled from the C parser keyed by the parsed function's *kernel*
name, and an inline body's kernel name carries an `#inline:<source>` suffix
while the sidecar names the function by its source spelling. Every
`static inline` function therefore looked like a function with no locals.

That was not a refusal with a name. A field whose layout is unknown lowers as
a width-unknown load, which defaults to a four-byte read, so `first->word` on
an eight-byte `unsigned long` member silently meant a different proposition
than the one written and the goal below was simply not proved; a masked read
such as `(first->word & 1) == 1` reported `missing pure fact: int32 equality is
true` for a member the contract states a 64-bit fact about. The layouts are now
keyed by the source spelling, which is what a sidecar writes; two definitions
sharing one source spelling leave no layouts rather than guessing between
them.

Both functions here declare the same local from the same declaration list. The
inline one is the regression; the ordinary one is the control that always
worked, and both read the member at its declared width.

```c filename=inline_local_layout.c
struct box {
    unsigned long word;
    struct box *next;
};

static inline void inline_reader(struct box *b)
{
    struct box *first = b, *second;

    second = first;
}

void ordinary_reader(struct box *b)
{
    struct box *first = b, *second;

    second = first;
}

void call_the_inline_one(struct box *b)
{
    inline_reader(b);
}
```

```click
verifying "inline_local_layout.c";

void inline_reader(struct box* b) {
    owns b->word;
    requires b != 0;
    requires b->word == 4294967296;
    ensures b->word == 4294967296;
} by {
    step();
    step();
    have first->word == 4294967296 by { simp(); }
    execute();
    simp();
}

void ordinary_reader(struct box* b) {
    owns b->word;
    requires b != 0;
    requires b->word == 4294967296;
    ensures b->word == 4294967296;
} by {
    step();
    step();
    have first->word == 4294967296 by { simp(); }
    execute();
    simp();
}

void call_the_inline_one(struct box* b) {
    owns b->word;
    requires b != 0;
    requires b->word == 4294967296;
    ensures b->word == 4294967296;
} by {
    execute();
    simp();
}
```

```expect
pass
```
