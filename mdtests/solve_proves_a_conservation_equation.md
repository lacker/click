# Machine conservation equations preserve bounds

The shrink proof uses the already-defined subtraction `capacity - amount`
to bound the equal expression `used + (available - amount)` in `Integer`.
The contract checks definedness explicitly because the word equality also
holds modulo 2^32. The grow theorem exercises the implicit closer on the
corresponding addition.

```click
import click::integer;

theorem shrink_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= amount;
    requires amount <= available;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity - amount);
    ensures defined(available - amount) and defined(used + (available - amount)) and
        capacity - amount == used + (available - amount) by {
        apply(integer::int32_nonnegative_subtract_within_value_is_defined(available, amount));
        apply(integer::int32_subtract_to_integer(available, amount));
        apply(integer::int32_subtract_to_integer(capacity, amount));
        apply(integer::int32_add_to_integer(used, available));
        have to_integer(used) + to_integer(available - amount) ==
                to_integer(capacity) - to_integer(amount) by {
            rewrite(to_integer(available - amount), to_integer(available) - to_integer(amount));
            rewrite(to_integer(capacity), to_integer(used) + to_integer(available));
            close();
        }
        have -2147483648 <= to_integer(used) + to_integer(available - amount) by {
            rewrite(to_integer(used) + to_integer(available - amount), to_integer(capacity) - to_integer(amount));
            close();
        }
        have to_integer(used) + to_integer(available - amount) <= 2147483647 by {
            rewrite(to_integer(used) + to_integer(available - amount), to_integer(capacity) - to_integer(amount));
            close();
        }
        have defined(used + (available - amount)) by { close(); }
        apply(integer::int32_add_to_integer(used, available - amount));
        have capacity - amount == used + (available - amount) by { close(); }
        close();
    }
}

theorem grow_conservation(capacity: int32, used: int32, available: int32, amount: int32) {
    requires 0 <= used;
    requires 0 <= available;
    requires 0 <= amount;
    requires capacity == used + available;
    requires defined(used + available);
    requires defined(capacity + amount);
    ensures defined(available + amount) and defined(used + (available + amount)) and
        capacity + amount == used + (available + amount) by {
        have to_integer(capacity) + to_integer(amount) <= 2147483647 by close();
        have to_integer(available) + to_integer(amount) <= 2147483647 by {
            close() using { 0 <= used; capacity == used + available; to_integer(capacity) + to_integer(amount) <= 2147483647; };
        }
        have -2147483648 <= to_integer(available) + to_integer(amount) by {
            close() using { 0 <= available; 0 <= amount; };
        }
        have defined(available + amount) by close();
        have defined(used + (available + amount)) by close();
        have capacity + amount == used + (available + amount) by close();
        close();
    }
}
```

```expect
pass
```
