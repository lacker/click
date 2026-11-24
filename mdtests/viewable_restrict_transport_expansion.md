# Viewability search expands to ordinary separation axioms

```c filename=first.c
int first(int *p, int n, int a, int b) { return p[0]; }
```

```click
import click::separation;
verifying "first.c";
int32 first(int32* p, int32 n, int32 a, int32 b) {
    requires 1 <= n;
    requires 0 <= a;
    requires a <= b;
    requires b <= n;
    views p[0..n];
    ensures result == p[0];
} by {
    have viewable(p[a..b]) by {
        close() using { viewable(p[0..n]); 0 <= a; a <= b; b <= n; };
    }
    step();
    close();
}
```

```expect
pass
```
