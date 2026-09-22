# Signed and unsigned 64-bit arrays in structs

Array fields keep eight-byte alignment and stride in C and in resource clauses.
Local copies and by-value calls preserve every element, including values outside
the 32-bit range. Partial initializers zero-fill the remaining elements.

```c filename=wide.c
struct wide { char tag; long signed_values[2]; unsigned long words[2][2]; int tail; };
struct wide global = {1, {-4294967296L}, {{4294967296UL}}};
unsigned long update(struct wide *p, unsigned long value) {
    p->words[1][1] = value;
    return p->words[1][0];
}
long update_signed(struct wide *p) {
    p->signed_values[1] = -4294967296L;
    return p->signed_values[1];
}
struct wide change(struct wide value) {
    value.words[1][1] = 4294967296UL;
    return value;
}
unsigned long local_copy(void) {
    struct wide a = {1, {-4294967296L}, {{4294967296UL}}};
    struct wide b = a;
    b = change(b);
    return a.words[1][1] + b.words[1][1] + b.words[0][1];
}
long static_zero(void) {
    static struct wide empty;
    return empty.signed_values[1];
}
long global_read(void) { return global.signed_values[0]; }
int main(void) { return static_zero() == 0; }
```

```click
verifying "wide.c" as wide;
unsigned long update(struct wide *p, unsigned long value) {
    views p->words[1][0];
    owns p->words[1][1];
    ensures result == old(p->words[1][0]) by auto;
    ensures p->words[1][1] == value by auto;
}
long update_signed(struct wide *p) {
    owns p->signed_values[0..2];
    ensures result == -4294967296 by auto;
}
struct wide change(struct wide value) {
    ensures result.signed_values[0] == value.signed_values[0] by auto;
    ensures result.words[1][1] == 4294967296u64 by auto;
    ensures result.words[0][1] == value.words[0][1] by auto;
    ensures result.words[1][1] + result.words[0][1] == 4294967296u64 + value.words[0][1] by auto;
}
unsigned long local_copy() {
    ensures result == 4294967296u64 by auto;
}

long static_zero() {
    views wide::static_zero::empty.signed_values;
    requires wide::static_zero::empty.signed_values[1] == 0;
    ensures result == 0 by auto;
}
int main() {
    ensures result == 1;
} by {
    have wide::static_zero::empty.signed_values[1] == 0 by simp;
    execute();
    simp();
}
long global_read() {
    views global.signed_values;
    ensures result == global.signed_values[0] by auto;
}
```

```expect
pass
```
