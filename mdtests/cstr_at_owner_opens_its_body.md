# An owner of a C string opens its body

`open(R(a)) { ... }` exposes one body layer of a held instance and folds it
back when the block ends. An owned `cstr_at` publishes a view of its own
bytes while it is held folded; that view borrows nothing, so its body facts
read the owner's memory, as they do after `unfold`. The same proof with
`views cstr_at(src, n);` opens a viewed instance
(`cstr_at_opens_and_lends_a_prefix_to_a_copy.md`).

```c filename=cstr_at_owner_opens_its_body.c
uint64 outer(uint8 *src, uint64 n)
{
	return 0;
}
```

```click
import click::c::string;
verifying "cstr_at_owner_opens_its_body.c";

uint64 outer(uint8* src, uint64 n) {
    owns cstr_at(src, n);
    requires 0u64 < n;
    ensures result == 0u64;
} by {
    open(cstr_at(src, n)) {
    }
}
```

```expect
pass
```
