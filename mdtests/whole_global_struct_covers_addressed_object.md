# A whole global struct covers the object passed by its address

```c filename=whole_global.c
struct pair { uint64 left; uint64 right; };
static struct pair state = { 3, 5 };
void set_pair(struct pair* p) { p->left = 7; p->right = 11; }
uint64 set_global() { set_pair(&state); return state.left + state.right; }
```
```click
verifying "whole_global.c";
void set_pair(struct pair* p) {
    owns *p;
    ensures p->left == 7u64;
    ensures p->right == 11u64;
}
uint64 set_global() {
    owns state;
    ensures result == 18u64;
} by { step_until(function.exit); close(); rewrite(state.left, 7u64); rewrite(state.right, 11u64); close(); }
```
```expect
pass
```
