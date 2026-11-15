# A borrowed composite's quantified fact opens after an unrelated write

The first statement changes the separately owned `q[0]`. Opening the borrowed
`nonzero(p, n)` at the resulting state must still publish its quantified
fact, which proves that the returned `p[0]` is nonzero.

```c filename=probe.c
int first(int p[], int n, int q[])
{
	q[0] = 1;
	return p[0];
}
```

```click
resource nonzero(p: int32*, n: int32) {
    views p[0..n];
    fact forall (k: int32) { 0 <= k and k < n implies p[k] != 0 };
}

verifying "probe.c";

int32 first(int32 p[], int32 n, int32 q[]) {
    requires 0 < n;
    views nonzero(p, n);
    owns q[0..1];
    ensures result != 0;
} by {
    step();
    open(nonzero(p, n)) {
    }
}
```

```expect
pass
```
