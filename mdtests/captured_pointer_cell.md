# Captured pointer arguments preserve the element type

Substituting a complete pointer value into an indexed resource retains its
declared element type. It grants no additional memory authority.

```c filename=probe.c
int32 probe(int32* p, int32 input) {
    p[0] = input;
    return input;
}
```
```click
verifying "probe.c";
resource cell(p: int32*) { owns p[0]; }
int32 probe(int32* p, int32 input) {
    owns cell(p);
    ensures result == input;
} by { unfold(cell(p)); execute(); fold(cell(p)); simp(); }
```
```expect
pass
```
