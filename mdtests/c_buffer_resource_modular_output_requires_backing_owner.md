# A C buffer output requires authority for its backing owner
```c filename=probe.c
struct buffer { int32* data; };
void init(struct buffer* owner, int32* data) { owner->data = data; }
void probe(struct buffer* owner, int32* data) { init(owner, data); }
```
```click
verifying "probe.c";
resource buffer(owner: struct buffer*) {
    owns owner->data;
    owns owner->data[0..1];
}
void init(struct buffer* owner, int32* data) {
    consumes *owner;
    produces buffer(owner);
    ensures owner->data == data;
} by { step_until(function.exit); fold(buffer(owner)); close(); }
void probe(struct buffer* owner, int32* data) {
    consumes *owner;
    produces buffer(owner);
    ensures owner->data == data;
}
```
```expect
fail: missing resource fact `owns owner->data[0..1]`
```
