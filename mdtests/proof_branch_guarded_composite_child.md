# Branch ensuring exports a child of a guarded composite

An owned guarded composite can expose a duplicable child through a checked
branch interface when the guard is established on both arms.

```c filename=select_guarded_left.c
int32 select_guarded_left(int32 key) {
    return key;
}
```

```c filename=select_guarded_right.c
int32 select_guarded_right(int32 key) {
    return key;
}
```

```c filename=select_guarded.c
int32 select_guarded(int32 key, int32 choose_left) {
    int32 selected;
    if (choose_left != 0) {
        selected = select_guarded_left(key);
    } else {
        selected = select_guarded_right(key);
    }
    return selected;
}
```

```click
abstract resource left_path(key: int32);
abstract resource right_path(key: int32);
abstract resource ready_permit(key: int32);

resource ready_bundle(key: int32) {
    if key >= 0 {
        contains ready_permit(key);
    }
}

verifying "select_guarded_left.c";
verifying "select_guarded_right.c";
verifying "select_guarded.c";

int32 select_guarded_left(int32 key) {
    consumes left_path(key);
    consumes ready_permit(key);

    produces ready_permit(key) by auto;
    ensures result == key by auto;
}

int32 select_guarded_right(int32 key) {
    consumes right_path(key);
    consumes ready_permit(key);

    produces ready_permit(key) by auto;
    ensures result == key by auto;
}

int32 select_guarded(int32 key, int32 choose_left) {
    requires key >= 0;
    consumes left_path(key);
    consumes right_path(key);
    consumes ready_permit(key);

    ensures result >= 0 by {
        step();
        branch {
            ensuring {
                fact selected == key;
                owns ready_bundle(key);
                views ready_permit(key);
            }
            then {
                step();
                fold(ready_bundle(key));
            }
            else {
                step();
                fold(ready_bundle(key));
            }
        }
        step();
        simp();
    }
}
```

```expect
pass
```
