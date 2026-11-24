# A call cannot reuse the member consumed by a quantity exchange

After the checked call the caller owns two surviving members. Spending
three must fail, even though the original input held three.

```c filename=quantity_exchange.c
void shrink(int32* counter) { *counter = *counter - 1; }
void lifecycle(int32* counter) { *counter = 3; shrink(counter); }
```

```click
authorized resource member(counter: int32*) {}
resource control(counter: int32*) {
    owns counter[0..1];
    owns authority(member(counter));
    fact counter[0] == count(member(counter));
}
verifying "quantity_exchange.c";
void shrink(int32* counter) {
    owns control(counter);
    consumes 2 of member(counter);
    produces member(counter);
    ensures count(member(counter)) == old(count(member(counter))) - 1;
} by {
    unfold(control(counter));
    unfold(2 of member(counter));
    step();
    fold(member(counter));
    fold(control(counter));
}
void lifecycle(int32* counter) {
    owns counter[0..1];
    owns authority(member(counter));
    requires count(member(counter)) == 0;
    ensures count(member(counter)) == 0;
} by {
    step();
    fold(3 of member(counter));
    fold(control(counter));
    step();
    have count(member(counter)) == 2 by close();
    unfold(control(counter));
    unfold(3 of member(counter));
}
```

```expect
fail: Requires owns member(p)
```
