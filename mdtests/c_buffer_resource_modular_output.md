# A C buffer resource survives a modular output call
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
    consumes data[0..1];
    produces buffer(owner);
    ensures owner->data == data;
} by { execute(); fold(buffer(owner)); simp(); }
void probe(struct buffer* owner, int32* data) {
    consumes *owner;
    consumes data[0..1];
    produces buffer(owner);
    ensures owner->data == data;
} by { execute(); simp(); }
```
```expect
pass
```
