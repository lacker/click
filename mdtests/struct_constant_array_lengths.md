# Constant-expression dimensions in structs

The CPU mask declaration retains the header's dimension expression. Constant
lengths also work in multiple dimensions and arrays of embedded structs.

```c filename=lengths.c
#define __CPU_SETSIZE 1024
#define __NCPUBITS (8 * sizeof(__cpu_mask))
typedef unsigned long int __cpu_mask;
typedef struct {
    __cpu_mask __bits[__CPU_SETSIZE / __NCPUBITS];
} cpu_set_t;
struct item { long value; };
struct packet {
    char tag;
    unsigned long words[1 + 1][sizeof(long) / 4];
    struct item items[8 / sizeof(long)][1 << 1];
};
int mask_size(void) { return sizeof(cpu_set_t); }
unsigned long update(struct packet *p) {
    p->words[1][1] = 4294967296UL;
    return p->words[1][1];
}
long local(void) {
    struct packet p = {1, {{0}}, {{ {3}, {7} }}};
    struct packet copy = p;
    copy.items[0][1].value = 9;
    return p.items[0][1].value + copy.items[0][1].value;
}
```

```click
verifying "lengths.c";
int mask_size() {
    ensures result == 128 by auto;
}
unsigned long update(struct packet *p) {
    owns p->words[1][1];
    ensures result == 4294967296u64 by auto;
}
long local() {
    ensures result == 16 by auto;
}
```

```expect
pass
```
