# A loop back edge does not return a composite whose body fact a store falsified

The loop keeps `owns zt(p)`, and its preserve proof unfolds the instance
before the body's C store falsifies the body fact `p[5] == 0`. The back edge
compares the body's bytes with the loop head's folded `zt(p)`; reading the
bytes as the instance is a fold, so it needs the fact. Otherwise the loop
returns `zt(p)` and `use` proves `result == 0` of a function returning 9
whenever `n > 0`.

```c filename=loop_returns_unchecked_composite.c
void spin(unsigned char *p, int n)
{
	int i = 0;
	while (i < n) {
		p[5] = 9;
		i = i + 1;
	}
}

unsigned char use(unsigned char *p, int n)
{
	spin(p, n);
	return p[5];
}
```

```click
resource zt(p: uint8*) {
    owns p[0..6];
    fact p[5] == 0;
}

verifying "loop_returns_unchecked_composite.c";

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

uint8 use(uint8* p, int32 n) {
    requires n >= 0;
    requires n < 100;
    owns zt(p);
    ensures result == 0;
} by {
    step();
    unfold(zt(p));
}
```

```expect
fail: loop state join changes resource ownership
```
