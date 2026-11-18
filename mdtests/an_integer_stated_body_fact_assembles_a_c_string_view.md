# An Integer-stated body fact assembles a C string view

A C string view `cstr_at(p, len)` is assembled from a local buffer's bytes
when the proof holds each of its body facts, among them
`forall (k: uint64) { 0u64 <= k and k < len + 1u64 implies defined(p[k]) }`,
read with C's `uint64` addition. A sidecar's arithmetic is Integer, so the
same fact written there reads `to_integer(k) < to_integer(len) + 1`. Below,
`len` is `n as uint64`, a value the proof knows only through `n == 2`. The
Integer fact states the C one once `len + 1u64` stays in range, which
`n as uint64 + 1 <= 18446744073709551615` gives, so the call to `snprintf`
assembles the view of `tmp` from it. Without that bound the view is refused
([`an_integer_stated_body_fact_needs_its_range_bound.md`](an_integer_stated_body_fact_needs_its_range_bound.md)).

```c filename=integer_stated_cstr.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);

int copy_name(char *buf, int n)
{
	char tmp[3];
	tmp[0] = 'a';
	tmp[1] = 'b';
	tmp[2] = '\0';
	return snprintf(buf, 8, "%s", tmp);
}
```

```click
import click::c::stdio;
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "integer_stated_cstr.c";

int32 copy_name(char buf[], int32 n) {
    requires n == 2;
    owns buf[0..8];
    ensures result == n;
} by {
    step();
    step();
    step();
    step();
    have n as uint64 + 1 <= 18446744073709551615;
    have tmp[n as uint64] == 0u8 by { solve(); }
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
    have forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) } by { enumerate(); }
    have forall (k: uint64) { 0u64 <= k and k < n as uint64 implies tmp[k] != 0u8 } by {
        intro();
        intro();
        have k < 2u64 by { solve(); }
        instantiate(forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 }, k);
        known();
    }
    have forall (k: uint64) { 0u64 <= k and k < n as uint64 + 1u64 implies defined(tmp[k]) } by {
        intro();
        intro();
        have k < 3u64 by { solve(); }
        instantiate(forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) }, k);
        known();
    }
    step(snprintf, { n0: n as uint64 });
}
```

```expect
pass
```
