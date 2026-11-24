# A pointer-table load at a masked index is not its first pointer alone

The masked index may select either stored pointer, so a claim that the load
always reads through the first is refused.

```c filename=k1.c
static const int a[2] = { 3, 4 };
static const int b[2] = { 5, 6 };
int f(unsigned int u)
{
	static const int *const t[] = { &a[0], &b[0] };
	return t[u & 1][1];
}
```

```click
verifying "k1.c";
int32 f(uint32 u) {
    ensures result == 4;
} by {
    step_until(function.exit);
    close();
}
```

```expect
fail: did not retain a complete proof
```
