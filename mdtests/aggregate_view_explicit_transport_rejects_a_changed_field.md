# A changed descriptor field is not preserved
```c filename=probe.c
struct Descriptor { int32 length; int32 *data; };
void write_first(struct Descriptor *owner) {
    owner->length = 7;
}
```
```click
verifying "probe.c";
void write_first(struct Descriptor *owner) {
    owns *owner;
    ensures owner->length == old(owner->length);
} by {
    step();
    have owner->length == old(owner->length) by { close(); }
    step_until(function.exit);
}
```
```expect
fail: `solve` failed
```
