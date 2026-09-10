# Owning the written file-scope cell authorizes the store without an effect clause

```c filename=owned_global.c
int32 words[2];
void set_second() { words[1] = 7; }
```

```click
verifying "owned_global.c";
void set_second() {
    owns words[1..2];
    ensures words[1] == 7 by auto;
}
```

```expect
pass
```
