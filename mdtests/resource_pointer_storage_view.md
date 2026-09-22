# Viewing a pointer slot does not grant access to its pointee

```c filename=pointer_storage.c
struct packet { int32* data; };
int32 read(struct packet* p) { return p->data[0]; }
```

```click
verifying "pointer_storage.c";
int32 read(struct packet* p) {
    views &p->data;
    ensures result == p->data[0];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
