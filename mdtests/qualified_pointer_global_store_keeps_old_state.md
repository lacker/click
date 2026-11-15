# Qualified global and static pointer reads respect current and old states

```c filename=exchange.c
struct pair { int value; };
static int anchor;
static struct pair* shared = 0;
struct pair* exchange_global(struct pair* p) {
    struct pair* previous = shared;
    shared = p;
    return previous;
}
int* exchange_static(int* p) {
    static int* slot = &anchor;
    int* previous = slot;
    slot = p;
    return previous;
}
```
```click
verifying "exchange.c" as unit;
struct pair* exchange_global(struct pair* p) {
    owns unit::shared;
    ensures unit::shared == p;
    ensures result == old(unit::shared);
}
int32* exchange_static(int32* p) {
    owns unit::exchange_static::slot;
    ensures unit::exchange_static::slot == p;
    ensures result == old(unit::exchange_static::slot);
}
```
```expect
pass
```
