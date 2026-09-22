# Anonymous struct typedefs preserve ordinary struct storage

The real glibc declaration has no tag. Its typedef names the same layout for
local objects, pointers, copies, and `sizeof`.

```c filename=anonymous.c
typedef struct { int __val[2]; } __fsid_t;
typedef __fsid_t fsid_alias;
typedef struct { char tag; int value; } *record_pointer;
int width(void) { return sizeof(__fsid_t); }
int use_local(void) {
    __fsid_t first = {{3, 7}};
    fsid_alias second = first;
    fsid_alias *p = &second;
    p->__val[0] = 11;
    return first.__val[0] + p->__val[0] + p->__val[1];
}
int pointer_alias(void) { return sizeof(record_pointer); }
```

```click
verifying "anonymous.c";
int width() { ensures result == 8 by auto; }
int use_local() { ensures result == 21 by auto; }
int pointer_alias() { ensures result == 8 by auto; }
```

```expect
pass
```
