# Viewability must not initialize an unread input cell

```c filename=viewable_defined_probe.c
void claim(int32 *p) {}
int32 probe(int32 *p) { claim(p); return *p; }
```

```click
verifying "viewable_defined_probe.c";
void claim(int32 *p) {
    requires viewable(p[0..1]);
    ensures defined(p[0]) by { have defined(p[0]) by { close(); } }
}
int32 probe(int32 *p) {
    owns uninitialized(p[0..1]);
    ensures result == result;
}
```

```expect
fail: could not establish
```
