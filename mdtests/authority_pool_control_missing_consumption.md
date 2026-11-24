# Pool control rejects missing consumption

The checkout increments the counter and produces an item. The final capacity
check rewrites the equation in terms of entry values so the arithmetic check
depends on whether the slot count actually decreased.

```c filename=pool_control.c
struct pool { int32 checked_out; int32 capacity; };
struct payload { int32 value; };
void checkout(struct pool* pool, struct payload* p) {
    pool->checked_out = pool->checked_out + 1;
}
```

```click
authorized resource slot(pool: struct pool*) {}
authorized resource item(pool: struct pool*, p: struct payload*) { owns *p; }
resource control(pool: struct pool*) {
    owns *pool;
    owns authority(slot(pool));
    owns authority(item(pool, _));
    fact 0 <= pool->checked_out;
    fact pool->checked_out == count(item(pool, _));
    fact pool->capacity == pool->checked_out + count(slot(pool));
}
verifying "pool_control.c";
void checkout(struct pool* pool, struct payload* p) {
    owns control(pool);
    requires pool->checked_out < 2147483647;
    consumes slot(pool);
    consumes *p;
    produces item(pool, p);
    ensures count(slot(pool)) == old(count(slot(pool))) - 1;
    ensures count(item(pool, _)) == old(count(item(pool, _))) + 1;
    ensures to_integer(pool->checked_out) == to_integer(old(pool->checked_out) + 1);
    ensures pool->capacity == old(pool->capacity);
} by {
    with(control(pool)) {
        have 1 <= to_integer(count(slot(pool))) by { close(); }
        have defined(pool->checked_out);
        have to_integer(pool->checked_out) + 1 <= 2147483647 by {
            close() using { to_integer(pool->checked_out) < 2147483647; };
        }
        have to_integer(pool->checked_out) + 1 >= -2147483648 by {
            close() using { 0 <= to_integer(pool->checked_out); };
        }
        have defined(pool->checked_out + 1) by { close(); }
        step();
        fold(item(pool, p));
        have to_integer(pool->capacity) == to_integer(old(pool->capacity)) by { close(); }
        have to_integer(old(pool->capacity)) ==
            to_integer(old(pool->checked_out)) + to_integer(old(count(slot(pool)))) by {
            close();
        }
        have to_integer(pool->checked_out) == to_integer(old(pool->checked_out)) + 1 by {
            close() using {
                to_integer(old(pool->checked_out)) + 1 <= 2147483647;
                to_integer(old(pool->checked_out)) + 1 >= -2147483648;
            };
        }
        have to_integer(pool->capacity) ==
            to_integer(pool->checked_out) + to_integer(count(slot(pool))) by {
            rewrite(to_integer(pool->capacity), to_integer(old(pool->capacity)));
            rewrite(to_integer(old(pool->capacity)),
                to_integer(old(pool->checked_out)) + to_integer(old(count(slot(pool)))));
            rewrite(to_integer(pool->checked_out), to_integer(old(pool->checked_out)) + 1);
            close() using { 1 <= to_integer(old(count(slot(pool)))); };
        }
    }
}

```

```expect
fail: `checkout.contract` proof step have body tactic 4: arithmetic read the current goal as an Integer linear claim; no combination of the listed premises proves it
```
