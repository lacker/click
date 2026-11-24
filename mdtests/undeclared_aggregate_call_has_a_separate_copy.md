# A cross-file aggregate call retains its value before copying

The caller has no local declaration of the callee. Its destination layout is
checked against the resolved function, and the result and copy are separate.

```c filename=producer.c
struct pair { int32 x; int32 y; };
struct pair make_pair() {
    struct pair p = {3, 4};
    return p;
}
```

```c filename=consumer.c
struct pair { int32 x; int32 y; };
int32 consume() {
    struct pair p = make_pair();
    return p.x + p.y;
}
```

```click
verifying "producer.c";
verifying "consumer.c";
struct pair make_pair() {
    ensures result.x == 3;
    ensures result.y == 4;
}
int32 consume() {
    ensures result == 7;
} by {
    step_until(statement(0).call(0).entry);
    step();
    have load<int32>(statement(0).call(0).result) == 3 by { close(); }
    step();
    have at(statement(0).assignment(p, 0).exit, p.x == 3) by { close(); }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
