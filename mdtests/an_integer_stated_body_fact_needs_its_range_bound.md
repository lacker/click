# An Integer-stated body fact needs its range bound

The negative of
[`an_integer_stated_body_fact_assembles_a_c_string_view.md`](an_integer_stated_body_fact_assembles_a_c_string_view.md),
without its `have n as uint64 + 1 <= 18446744073709551615`. The Integer fact
`to_integer(k) < to_integer(len) + 1` states the C fact `k < len + 1u64` only
when `len + 1u64` does not wrap, so with no bound on `len` the view of `tmp`
is not assembled from it.

```c filename=integer_stated_cstr_unbounded.c
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
verifying "integer_stated_cstr_unbounded.c";

int32 copy_name(char buf[], int32 n) {
    requires n == 2;
    owns buf[0..8];
    ensures result == n;
} by {
    step();
    step();
    step();
    step();
    have forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 } by { enumerate(); }
    have forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) } by { enumerate(); }
    have forall (k: uint64) { 0u64 <= k and k < n as uint64 implies tmp[k] != 0u8 } by {
        intro();
        intro();
        have k < 2u64 by { close(); }
        instantiate(forall (k: uint64) { 0u64 <= k and k < 2u64 implies tmp[k] != 0u8 }, k);
        close();
    }
    have forall (k: uint64) { 0u64 <= k and k < n as uint64 + 1u64 implies defined(tmp[k]) } by {
        intro();
        intro();
        have k < 3u64 by { close(); }
        instantiate(forall (k: uint64) { 0u64 <= k and k < 3u64 implies defined(tmp[k]) }, k);
        close();
    }
    step(snprintf, { n0: n as uint64 });
}
```

```expect
fail: requires an exact body fact
```
