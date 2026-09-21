# Earlier invariant guards do not consume the user's introductions

Splitting the bounds into separate declarations must not change the proof of
the empty prefix. Initialization retains the checked guarded form of every
earlier invariant, so the universal proof still introduces only its written
binder and range guard. The C is the unchanged symbolic-empty-range fixture.

```c filename=probe_fill.c
int32 probe_fill(int32 p[], int32 lo, int32 hi, int32 v) {
    int32 i;
    i = lo;
    while (i < hi) {
        p[i] = v;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "probe_fill.c";

int32 probe_fill(int32 p[], int32 lo, int32 hi, int32 v) {
    requires 0 <= lo and lo <= hi and hi <= 1000;
    owns p[lo..hi];
    ensures result == hi;
    ensures forall (k: int32) { lo <= k and k < hi implies p[k] == v };
} by {
    step();
    step();
    loop as fill {
        decreases hi - i;
        invariant lo <= i;
        invariant i <= hi;
        invariant forall (k: int32) { lo <= k and k < i implies p[k] == v };

        initialize by {
            have lo <= i by { normalize(); }
            have i <= hi by { assumption(); }
            have forall (k: int32) { lo <= k and k < i implies p[k] == v } by {
                intro();
                intro();
                contradiction(lo <= k and k < i);
            }
        }
        preserve by {
            have 0 <= i by {
                extract(0 <= lo);
                apply(int32_le_transitive(0, lo, i)) using { 0 <= lo; lo <= i; }
            }
            have 0 <= hi by {
                extract(0 <= lo);
                extract(lo <= hi);
                apply(int32_le_transitive(0, lo, hi)) using { 0 <= lo; lo <= hi; }
            }
            have 0 <= hi - i - 1 by {
                extract(hi <= 1000);
                arithmetic() using { i < hi; 0 <= i; 0 <= hi; hi <= 1000; }
            }
            have hi - i - 1 < hi - i by {
                extract(hi <= 1000);
                arithmetic() using { i < hi; 0 <= i; 0 <= hi; hi <= 1000; }
            }
            step();
            step();
            simp();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
