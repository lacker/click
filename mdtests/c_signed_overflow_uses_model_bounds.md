```c filename=read.c
struct cell { int32 value; };
int32 f(struct cell* p) { int32 total = 1; total += p->value; return total; }
```
```click
verifying "read.c";
resource modeled(p: struct cell*) {
    field number: int32;
    owns p->value;
    fact p->value == number;
}
int32 f(struct cell* p) {
    owns cell: modeled(p);
    requires 0 <= cell.number;
    requires cell.number <= 2147483646;
    ensures result == 1 + old(cell.number);
} by { unfold(cell); execute(); fold(cell); simp(); }
```
```expect
pass
```
