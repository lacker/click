# Owning one file-scope cell does not authorize storing into its neighbor

```c filename=neighbor_global.c
int32 words[2];
void set_second() { words[1] = 7; }
```

```click
verifying "neighbor_global.c";
void set_second() {
    owns words[0..1];
    ensures words[1] == 7 by auto;
}
```

```expect
fail: outside the owned footprint
```
