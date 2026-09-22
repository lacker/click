# A copied parameter does not borrow the caller's field storage

```c filename=parameter_storage.c
struct packet { int32* data; };
int32 read(struct packet input) { return input.data[0]; }
```

```click
verifying "parameter_storage.c";
int32 read(struct packet input) {
    views &input.data;
    views input.data[0..1];
    ensures result == input.data[0];
} by { execute(); simp(); }
```

```expect
fail: its private storage cannot be an input resource
```
