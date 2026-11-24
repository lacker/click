# An exact read grants no access

`exact(p[0])` reads the same cell as `p[0]`, named by the state in scope
(`design/exact-reads.md`). Like the ordinary read, it is a logical read: it
grants no permission and adds no resource. After the proof names
`exact(p[0])`, the C read `*p` still needs `views p[0]`, which `get` does
not hold, and is refused as it is without the `have`.

```c filename=an_exact_read_grants_no_access.c
int get(int *p) { return *p; }
```

```click
verifying "an_exact_read_grants_no_access.c";
int32 get(int32* p) {
    ensures result == p[0];
} by {
    have exact(p[0]) == exact(p[0]) by close();
    step_until(function.exit);
}
```

```expect
fail: `step()` could not verify C operation: missing resource fact `views p[0]`
```
