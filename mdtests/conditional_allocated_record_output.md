# Conditional allocated-record output is reusable without deciding its guard
```c filename=probe.c
struct box { int32 value; };
struct box* create(int32 value) {
    struct box* p = malloc(sizeof(struct box));
    if (p != 0) { p->value = value; }
    return p;
}
void dispose(struct box* p) { if (p != 0) { free(p); } }
int32 probe(int32 value) {
    struct box* p = create(value);
    dispose(p);
    return 0;
}
```
```click
verifying "probe.c";
resource box(p: struct box*) {
    if p != 0 {
        owns allocation(p, sizeof(struct box));
        owns *p;
    }
}
struct box* create(int32 value) {
    produces box(result);
} by { execute(); fold(box(result)); simp(); }
void dispose(struct box* p) {
    consumes box(p);
} by {
    if p != 0 { unfold(box(p)); execute(); simp(); }
    else { unfold(box(p)); execute(); simp(); }
}
int32 probe(int32 value) {
    ensures result == 0;
} by { execute(); simp(); }
```
```expect
pass
```
