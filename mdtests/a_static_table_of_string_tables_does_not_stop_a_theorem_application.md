# A static table of string tables does not stop a theorem application

`string_get_size` keeps `static const char *const *const units_str[]`, a table
of pointers to string tables. Click has no pointer type for its first
element's address, `const char *const *const *`, so a proof cannot name the
table as a value; execution reads it all the same. Applying a theorem at an
execution frontier that has such a table in scope used to stop the verifier
with a panic while it gathered the frame's arrays for the proof's names. The
table is now left out of those names, and the application proceeds.

```c filename=a_static_table_of_string_tables_does_not_stop_a_theorem_application.c
int f(void)
{
	static const char *const a[] = { "", "k" };
	static const char *const *const t[] = { a, a };
	int x;

	x = 0;
	return x;
}
```

```click
import click::c::stdio;
verifying "a_static_table_of_string_tables_does_not_stop_a_theorem_application.c";

int32 f() {
    ensures result == 0;
} by {
    have stdio::decimal_length(0u64) == 1u64 by {
        apply(stdio::decimal_length_1(0u64));
    }
}
```

```expect
pass
```
