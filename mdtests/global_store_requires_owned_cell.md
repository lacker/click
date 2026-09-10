# A view of file-scope storage does not authorize a store into it

A contract that declares resources but no effect clause frames caller memory
through the resource transition at each store. File-scope and static storage is
not external memory, so its writes are framed by the owned footprint instead:
a function that only views a global cell must not store into it.

```c filename=viewed_global.c
int32 words[2];
void set_second() { words[1] = 7; }
```

```click
verifying "viewed_global.c";
void set_second() {
    views words[1..2];
    ensures words[1] == 7 by auto;
}
```

```expect
fail: outside the owned footprint
```
