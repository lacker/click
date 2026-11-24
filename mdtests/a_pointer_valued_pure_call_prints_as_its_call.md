# A pointer-valued pure call prints as its call

A goal about the result of a pure function returning a pointer prints that
result as the call, so it can be written back into a proof. Before, it
printed as `<pointer A>`, a label the report never defined. The array argument
retains its entry-state spelling in the reported goal.

```c filename=a_pointer_valued_pure_call_prints_as_its_call.c
unsigned char first(const unsigned char *p, unsigned long n)
{
	return p[0];
}
```

```click
verifying "a_pointer_valued_pure_call_prints_as_its_call.c";

function opaque_first(p: uint8*, n: uint64) -> uint8* {
    p
}

uint8 first(const uint8* p, uint64 n) {
    requires 1u64 <= n;
    requires n <= 4096u64;
    views p[0..n];
    ensures result == p[0];
} by {
    have opaque_first(p, n) == p + 1;
    step_until(function.exit);
    close();
}
```

```expect
fail: goal: opaque_first(old(p), n) == &p[1]
```
