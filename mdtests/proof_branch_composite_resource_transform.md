# Branch ensuring joins different resource transformations

Each branch consumes a different path token through a helper call. Both calls
return the same permit, which is folded into `ready_bundle`. The branch exports
the common bundle at its ordinary continuation, and `observe` recovers the
nonnegative-key fact from that composite resource.

```c filename=select_left.c
int32 select_left(int32 key) {
    return key;
}
```

```c filename=select_right.c
int32 select_right(int32 key) {
    return key;
}
```

```c filename=select_ready.c
int32 select_ready(int32 key, int32 choose_left) {
    int32 selected;
    if (choose_left != 0) {
        selected = select_left(key);
    } else {
        selected = select_right(key);
    }
    return selected;
}
```

```click
abstract resource left_path(key: int32);
abstract resource right_path(key: int32);
abstract resource ready_permit(key: int32);

resource ready_bundle(key: int32) {
    owns ready_permit(key);
    fact key >= 0;
}

verifying "select_left.c";
verifying "select_right.c";
verifying "select_ready.c";

int32 select_left(int32 key) {
    consumes left_path(key);
    owns ready_permit(key);

    ensures result == key;
}

int32 select_right(int32 key) {
    consumes right_path(key);
    owns ready_permit(key);

    ensures result == key;
}

int32 select_ready(int32 key, int32 choose_left) {
    requires key >= 0;
    consumes left_path(key);
    consumes right_path(key);
    consumes ready_permit(key);

    ensures result >= 0 by {
        step();
        branch ensuring {
            fact selected == key;
            owns ready_bundle(key);
        } {
            true => {
                step();
                step();
                fold(ready_bundle(key));
            }
            false => {
                step();
                step();
                fold(ready_bundle(key));
            }
        }
        observe(ready_bundle(key));
        step();
        close();
    }
}
```

```expect
pass
```
