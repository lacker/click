# A global byte cell does not authorize its neighbor

```c filename=byte_neighbor.c
uint8 bytes[2];
void set_second() { bytes[1] = 7; }
```

```click
verifying "byte_neighbor.c";
void set_second() {
    owns bytes[0..1];
    views bytes[1..2];
    ensures bytes[1] == 7 by auto;
}
```

```expect
fail: outside the owned footprint
```
