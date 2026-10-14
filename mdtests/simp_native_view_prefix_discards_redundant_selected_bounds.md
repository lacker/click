# Native view simplification retains only necessary connected premises

Redundant bounds on the same native count must not exhaust the 64-premise
source-spelling limit. The entire selected proof context is checked.

```c filename=prefix.c
void prefix(const unsigned char *p, unsigned long held) {}
```

```click
target "x86_64-linux-userspace";
verifying "prefix.c";
void prefix(const uint8* p, uint64 held) {
 requires 1u64 <= held;
 requires held <= 5551u64;
 requires held <= 10000u64;
 requires held <= 10001u64;
 requires held <= 10002u64;
 requires held <= 10003u64;
 requires held <= 10004u64;
 requires held <= 10005u64;
 requires held <= 10006u64;
 requires held <= 10007u64;
 requires held <= 10008u64;
 requires held <= 10009u64;
 requires held <= 10010u64;
 requires held <= 10011u64;
 requires held <= 10012u64;
 requires held <= 10013u64;
 requires held <= 10014u64;
 requires held <= 10015u64;
 requires held <= 10016u64;
 requires held <= 10017u64;
 requires held <= 10018u64;
 requires held <= 10019u64;
 requires held <= 10020u64;
 requires held <= 10021u64;
 requires held <= 10022u64;
 requires held <= 10023u64;
 requires held <= 10024u64;
 requires held <= 10025u64;
 requires held <= 10026u64;
 requires held <= 10027u64;
 requires held <= 10028u64;
 requires held <= 10029u64;
 requires held <= 10030u64;
 requires held <= 10031u64;
 views p[0u64..held];
 ensures viewable(p[0u64..1u64]);
} by {
 have viewable(p[0u64..held]) by simp();
 have viewable(p[0u64..1u64]) by simp();
 execute(); assumption();
}
```

```expect
pass
```
