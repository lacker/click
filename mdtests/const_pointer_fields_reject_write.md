# Pointee const on a field rejects writes through that field

```c filename=main.c
struct holder { const char *text; };
int bad(struct holder *h) { h->text[0] = 1; return 0; }
```

```click
verifying "main.c";
```

```expect
fail:const-qualified
```
