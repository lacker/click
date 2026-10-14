# A theorem application cites a recorded historical byte equality
```c filename=recorded.c
void f(const unsigned char *p, int index) {}
```
```click
target "x86_64-linux-userspace";
verifying "recorded.c";
theorem same_byte(left: uint8, right: uint8) {
 requires (int32)left == (int32)right;
 ensures left == right by { assumption(); }
}
void f(const uint8* p, int32 index) {
 requires index == 0;
 views p[0u64..1u64];
 ensures index == 0;
} by {
 have p[0] == old(p)[index] by simp();
 apply(same_byte(p[0], old(p)[index]));
 execute(); assumption();
}
```
```expect
pass
```
