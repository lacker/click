# GNU type compatibility keeps source identity and does not read its operands

The struct comparisons are the form used by Linux `container_of`: the operand
of `typeof` names a dereferenced pointer or an embedded member. Neither is a
runtime read. The scalar comparisons distinguish C types with identical sizes.

```c filename=compatible.c
struct rb_node { int32 color; };
struct holder { struct rb_node node; };
struct other { int32 color; };
typedef struct rb_node node_t;
typedef long long wide_t;

int32 same(struct rb_node* p) {
    return __builtin_types_compatible_p(typeof(*p), typeof(((struct holder*)0)->node));
}
int32 other(struct rb_node* p) {
    return __builtin_types_compatible_p(typeof(*p), struct other);
}
int32 is_void(struct rb_node* p) {
    return __builtin_types_compatible_p(typeof(*p), void);
}
int32 aliases() {
    return __builtin_types_compatible_p(node_t, struct rb_node)
        && __builtin_types_compatible_p(wide_t, long long);
}
int32 untouched(struct rb_node* p) {
    int32 compatible = __builtin_types_compatible_p(typeof(*(p++)), struct rb_node);
    return compatible && p == 0;
}
int32 assigned() {
    int32 compatible = 0;
    compatible = __builtin_types_compatible_p(int, int);
    return compatible;
}
int32 rank() { return __builtin_types_compatible_p(long, long long); }
int32 top_const() { return __builtin_types_compatible_p(const int*, const int* const); }
int32 pointee_const() { return __builtin_types_compatible_p(int*, const int*); }
```

```click
verifying "compatible.c";
int32 same(struct rb_node* p) { ensures result == 1 by { execute(); normalize(); } }
int32 other(struct rb_node* p) { ensures result == 0 by { execute(); normalize(); } }
int32 is_void(struct rb_node* p) { ensures result == 0 by { execute(); normalize(); } }
int32 aliases() { ensures result == 1 by { execute(); normalize(); } }
int32 untouched(struct rb_node* p) {
    requires p == 0;
    ensures result == 1 by { execute(); normalize(); }
}
int32 assigned() { ensures result == 1 by { execute(); normalize(); } }
int32 rank() { ensures result == 0 by { execute(); normalize(); } }
int32 top_const() { ensures result == 1 by { execute(); normalize(); } }
int32 pointee_const() { ensures result == 0 by { execute(); normalize(); } }
```

```expect
pass
```
