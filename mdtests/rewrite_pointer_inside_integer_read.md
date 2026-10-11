# Pointer rewriting inside mathematical byte observations

The scalar tail of the unchanged Rust Adler checksum needs to relate its
iterator cursor to the original slice index. A byte read inside `to_integer`
keeps its load identity; rewriting must follow that identity's address without
changing its memory snapshot or byte width.

```c filename=integer_pointer_reads.c
struct inner { unsigned char* cells; };
struct outer { struct inner* in; };
int same(struct outer* o, struct inner* a) { return 0; }
```

```click
verifying "integer_pointer_reads.c";
theorem tail_pointer_read(p: const uint8*, bytes: uint8[], n: uint64) {
 requires p == bytes + n;
 ensures to_integer((int32)p[0]) == to_integer((int32)(bytes + n)[0]) by {
  rewrite(p == bytes + n);
  normalize();
 }
}
theorem tail_wide_pointer_read(p: const uint8*, bytes: uint8[], n: uint64) {
 requires p == bytes + n;
 ensures to_integer((uint64)p[0]) == to_integer((uint64)(bytes + n)[0]) by {
  rewrite(p == bytes + n);
  normalize();
 }
}
theorem loaded_byte_read(o: struct outer*, a: struct inner*) {
 requires o->in == a;
 ensures to_integer((int32)o->in->cells[2]) == to_integer((int32)a->cells[2]) by {
  rewrite(o->in == a);
  normalize();
 }
}

```

```expect
pass
```
