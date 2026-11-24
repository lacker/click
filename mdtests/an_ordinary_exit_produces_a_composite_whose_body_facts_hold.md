# An ordinary exit produces a composite whose body facts hold

The twin of
`an_ordinary_exit_does_not_produce_a_composite_whose_body_fact_a_store_falsified.md`:
the C store now makes the body fact `p[5] == 0` true. `mk` folds `zt(p)`
explicitly; `mk_at_exit` leaves the fold to its ordinary exit, which
assembles `zt(p)` from the owned bytes because the fact holds there; `mk_from`
establishes the fact from its precondition rather than a constant store.
`spin` keeps `owns zt(p)` around a loop whose preserve proof unfolds it and
never refolds; its back edge reads the bytes as `zt(p)` again because the
store keeps the fact. `use` unfolds the produced instance and reads the fact.

```c filename=exit_produces_checked_composite.c
void mk(unsigned char *p)
{
	p[5] = 0;
}

void mk_at_exit(unsigned char *p)
{
	p[5] = 0;
}

void mk_from(unsigned char *p, unsigned char v)
{
	p[5] = v;
}

void spin(unsigned char *p, int n)
{
	int i = 0;
	while (i < n) {
		p[5] = 0;
		i = i + 1;
	}
}

unsigned char use(unsigned char *p)
{
	mk(p);
	return p[5];
}
```

```click
resource zt(p: uint8*) {
    owns p[0..6];
    fact p[5] == 0;
}

verifying "exit_produces_checked_composite.c";

void mk(uint8* p) {
    consumes p[0..6];
    produces zt(p);
}

void mk_at_exit(uint8* p) {
    consumes p[0..6];
    produces zt(p);
}

void mk_from(uint8* p, uint8 v) {
    requires v == 0;
    consumes p[0..6];
    produces zt(p);
}

void spin(uint8* p, int32 n) {
    requires n >= 0;
    requires n < 100;
    owns zt(p);
} by {
    step_until(loop(0).entry);
    loop {
        owns zt(p);
        invariant i >= 0;
        invariant i <= n;
        decreases n - i;
        initialize by close();
        maintain by {
            unfold(zt(p));
            step();
            step();
        }
    }
}

uint8 use(uint8* p) {
    owns p[0..6];
    ensures result == 0;
} by {
    step();
    unfold(zt(p));
}
```

```expect
pass
```
