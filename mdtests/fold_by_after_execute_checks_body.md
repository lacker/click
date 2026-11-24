# A post-execution fold checks its source body proof

The body proof must be expanded and checked before it becomes part of the
return resource certificate.

```c filename=probe.c
int32 probe(int32 n, int32 m) { return 0; }
```

```click
verifying "probe.c";
resource either(n: int32, m: int32) { fact n > 0 or m > 0; }
int32 probe(int32 n, int32 m) {
    requires n > 0;
    produces either(n, m);
    ensures result == 0;
} by {
    step_until(function.exit);
    fold(either(n, m)) by { close(); }
    close();
}
```

```expect
pass
```
