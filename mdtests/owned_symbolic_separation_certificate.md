# Separation of owned symbolic ranges has a checkable certificate

```c filename=attach.c
struct holder { int32 len; int32* data; };
void attach(struct holder* owner, int32* data, int32 length) {
    owner->len = length;
    owner->data = data;
}
```

```click
verifying "attach.c";
void attach(struct holder* owner, int32* data, int32 length) {
    requires 1 <= length;
    owns object(owner);
    owns data[0..length];
    ensures owner->data == data;
} by {
    have separate(memory(object(owner)), memory(data[0..length])) by { assumption(); }
    execute();
    simp();
}
```

```expect
pass
```
