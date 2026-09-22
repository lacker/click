# Integer specifier order

The size_t typedef preserves GCC's header spelling. C and Click declarations
share the same integer spelling rules, without changing widths or signedness.

```c filename=integer_order.c
typedef long unsigned int size_t;
size_t preserve(size_t value) { return value; }
signed int short promote(int signed short value) { return value; }
long unsigned long int wide(long int unsigned long value) { return value; }
unsigned maximum(void) { return (int unsigned)4294967295; }
int widths(void) {
    return sizeof(long unsigned int) + sizeof(int short signed)
        + sizeof(char signed) + sizeof(long int unsigned long);
}
```

```click
verifying "integer_order.c";
int long unsigned preserve(long unsigned int value) {
    ensures result == value;
} by { execute(); simp(); }
int short signed promote(short int signed value) {
    ensures result == value;
} by { execute(); simp(); }
long unsigned int long wide(int long long unsigned value) {
    ensures result == value;
} by { execute(); simp(); }
unsigned maximum() {
    ensures result == 4294967295;
} by { execute(); simp(); }
int widths() {
    ensures result == 19;
} by { execute(); simp(); }
```

```expect
pass
```
