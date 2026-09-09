# Function-qualified static ownership crosses calls without being recreated

```c filename=counter.c
uint32 calls = 99;
uint32 increment(void) {
    static uint32 calls = 5;
    calls += 1;
    return calls;
}
uint32 other(void) {
    static uint32 calls = 20;
    calls += 1;
    return calls;
}
```

```c filename=main.c
uint32 increment(void);
uint32 other(void);
uint32 twice(void) { increment(); return increment(); }
int main(void) { twice(); other(); return 0; }
```

```click
verifying "counter.c" as counter_file;
verifying "main.c";

uint32 increment() {
    owns &counter_file::increment::calls[0..1];
    ensures counter_file::increment::calls == old(counter_file::increment::calls) + 1u32;
    ensures result == old(counter_file::increment::calls) + 1u32;
    ensures result == counter_file::increment::calls;
} by { execute(); simp(); }
uint32 other() {
    owns &counter_file::other::calls[0..1];
    ensures counter_file::other::calls == old(counter_file::other::calls) + 1u32;
    ensures result == old(counter_file::other::calls) + 1u32;
} by { execute(); simp(); }
uint32 twice() {
    owns &counter_file::increment::calls[0..1];
    ensures result == (old(counter_file::increment::calls) + 1u32) + 1u32;
    ensures counter_file::increment::calls == (old(counter_file::increment::calls) + 1u32) + 1u32;
} by {
    step();
    have counter_file::increment::calls == old(counter_file::increment::calls) + 1u32 by simp;
    execute();
    simp();
}
int main() {
    ensures counter_file::increment::calls == 7u32;
    ensures counter_file::other::calls == 21u32;
    ensures counter_file::calls == 99u32;
} by {
    have counter_file::increment::calls == 5u32 by simp;
    have counter_file::other::calls == 20u32 by simp;
    step();
    have counter_file::increment::calls == 7u32 by simp;
    execute();
    simp();
}
```

```expect
pass
```
