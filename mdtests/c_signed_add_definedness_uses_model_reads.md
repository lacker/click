```c filename=reads.c
struct cell { int32 value; };
int32 f(struct cell* p, struct cell* q) {
    int32 total = 1;
    total += p->value;
    total += q->value;
    return total;
}
```
```click
verifying "reads.c";
resource modeled(p: struct cell*) {
    field number: int32;
    owns p->value;
    fact p->value == number;
}
int32 f(struct cell* p, struct cell* q) {
    owns left: modeled(p);
    owns right: modeled(q);
    requires 0 <= left.number;
    requires left.number <= 2147483646;
    requires defined(1 + left.number + right.number);
    ensures result == 1 + old(left.number) + old(right.number);
} by {
    unfold(left); unfold(right);
    execute();
    fold(left); fold(right); simp();
}
```
```expect
pass
```
