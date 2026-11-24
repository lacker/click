# An aliased checkout cannot obtain a second copy of private memory

```c filename=pool_alias.c
void issue(int32* pool, int32* p) {}
void duplicate(int32* pool, int32* p) { issue(pool, p); issue(pool, p); }
```

```click
authorized resource member(pool: int32*, p: int32*) { owns p[0..1]; }
resource control(pool: int32*) {
    owns pool[0..1];
    owns authority(member(pool, _));
}
verifying "pool_alias.c";
void issue(int32* pool, int32* p) {
    owns control(pool);
    consumes p[0..1];
    requires defined(count(member(pool, _)) + 1);
    produces member(pool, p);
    ensures to_integer(count(member(pool, _))) == to_integer(old(count(member(pool, _))) + 1);
} by {
    with(control(pool)) { fold(member(pool, p)); }
}
void duplicate(int32* pool, int32* p) {
    owns control(pool);
    consumes p[0..1];
    requires to_integer(count(member(pool, _))) == 0;
    produces 2 of member(pool, p);
} by {
    have defined(count(member(pool, _)) + 1) by close();
    step();
    have to_integer(count(member(pool, _))) == 1 by close();
    have defined(count(member(pool, _)) + 1) by close();
    step();
}
```

```expect
fail: population helper member transition refused
```
