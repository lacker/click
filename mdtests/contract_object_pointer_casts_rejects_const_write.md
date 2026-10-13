# A cast cannot turn a const borrow into write permission

```c filename=const.c
struct base { int32 tag; };
struct item { struct base base; int32 value; };
void write(const struct base* p) {
    struct item* item = (struct item*)(void*)p;
    item->value = 1;
}
```

```click
verifying "const.c";
void write(const struct base* p) {
    views ((struct item*)(void*)p)->value;
    ensures ((struct item*)(void*)p)->value == 1;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
