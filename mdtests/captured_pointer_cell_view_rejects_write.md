# Captured pointer arguments preserve views without granting write authority

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
resource cell(p: int32*) { views p[0]; }
int32 probe(int32* p, int32 input) {
    views cell(p);
    ensures result == input;
} by { unfold(cell(p)); execute(); fold(cell(p)); simp(); }
```
```expect
fail: missing resource fact `owns p[0]`
```
