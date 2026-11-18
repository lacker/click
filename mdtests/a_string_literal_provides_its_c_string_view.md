# A string literal provides its C-string view

A string literal is a read-only array that holds its bytes and a terminator
(C11 6.4.5p6), so it is a C string by construction. A call whose contract
views `click::c::string::cstr_at(p, _)` for a pointer into a literal takes the view
from the literal itself: the literal's bytes decide the resource's body facts
and fix its `len`, and nothing can write them, so the view is read authority
the caller always has, never a loan.

`strlen("abc")`, a pointer into a literal, `%s` of a literal, and the
literal a conditional or a table chooses each take it, as do calls in the
program entry.

```c filename=literal_views.c
int snprintf(char *buf, unsigned long size, const char *fmt, ...);
unsigned long strlen(const char *s);

unsigned long measured(void)
{
	return strlen("abc");
}

unsigned long tail(void)
{
	return strlen("abc" + 1);
}

int unit(char *buf)
{
	return snprintf(buf, 8, "%s", "kB");
}

int separator(char *buf, int no_space)
{
	return snprintf(buf, 8, "%s", no_space ? "" : " ");
}

int prefix(char *buf, int i)
{
	static const char *const units_10[] = { "", "k", "M" };

	return snprintf(buf, 8, "%s", units_10[i]);
}
```

```click
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "literal_views.c";

uint64 measured() {
    ensures result == 3u64;
}

uint64 tail() {
    ensures result == 2u64;
}

int32 unit(char buf[]) {
    owns buf[0..8];
    ensures result == 2;
}

int32 separator(char buf[], int32 no_space) {
    owns buf[0..8];
    ensures (no_space != 0 and result == 0) or (no_space == 0 and result == 1);
}

int32 prefix(char buf[], int32 i) {
    requires i == 1;
    owns buf[0..8];
    ensures result == 1;
}
```

```expect
pass
```
