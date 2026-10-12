# Checked unreachable calls do not require termination of their callees

The second caller learns its branch is unreachable from a checked call
contract. The linked helper intentionally has no termination proof.

```c filename=unreachable.c
static void spin(void) { while (1) {} }
int off(void) { return 0; }
void caller(int flag) { if (flag) spin(); }
void after_call(void) { if (off()) spin(); }
```
```click
verifying "unreachable.c";
int32 off() { ensures result == 0; } by { execute(); simp(); }
void caller(int32 flag) {
    requires flag == 0;
    ensures 1 == 1;
} by { execute(); simp(); }
void after_call() { ensures 1 == 1; } by { execute(); simp(); }
```
```expect
pass
```
