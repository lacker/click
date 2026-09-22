# A pointer-field assignment still modifies the private parameter copy

```c filename=pointer_field_mutation.c
struct packet { int32* data; };
int32 redirect(struct packet input, int32* other) {
    input.data = other;
    return 0;
}
```

```click
verifying "pointer_field_mutation.c";
int32 redirect(struct packet input, int32* other) {
    ensures input.data == other;
} by { execute(); simp(); }
```

```expect
fail: by-value aggregate parameter `input` is modified
```
