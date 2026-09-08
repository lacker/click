# Alternative owned postconditions are not duplicated

Even identical ownership promises are not added as independently spendable
resources. General resource conjunction is an explicit deferred capability.

```c filename=joint.c
void invoke(void (*callback)(int32*), int32* cell) { callback(cell); }
```

```click
contract void First(int32* cell) { owns cell[0..1]; }
contract void Second(int32* cell) { owns cell[0..1]; }
verifying "joint.c";
void invoke(void (*callback)(int32*), int32* cell) {
    requires First(callback);
    requires Second(callback);
    owns cell[0..1];
} by { execute(); frame(); }
```

```expect
fail: combining resource-bearing callback contracts is not yet supported
```
