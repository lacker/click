# Crowded store ownership uses explicit transport

Several owned ranges share each written base. Automatic preservation may
forget the cached read instead of searching those members; the proof selects
the two cells and carries their value across the store explicitly.

```c filename=put.c
void put(int32* p, int32* q) {
    q[0] = 7;
}
```
```click
verifying "put.c";
void put(int32* p, int32* q) {
    owns p[0..1];
    owns p[2..3];
    owns q[0..1];
    owns q[2..3];
    requires p[0] == 9;
    ensures p[0] == 9;
} by {
    have separate(memory(p[0]), memory(q[0])) by { close(); }
    step();
    have p[0] == 9 by {
        have p[0] == 9 by {
            close() using {
                old(p[0]) == 9;
            };
        }
        close();
    }
}
```
```expect
pass
```
