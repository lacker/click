# A resource field can select a memory-range endpoint

A scalar resource field is stable model data while its resource is folded, in
the same way a matched constructor payload is. The field can therefore select
a symbolic suffix and bound a quantified fact over that suffix: folding takes
the endpoint as the proposed field value, and unfolding publishes the folded
field value as the endpoint. This is the plain-field twin of
[`resource_match_payload_memory_endpoint.md`](resource_match_payload_memory_endpoint.md),
with no `spec enum` or `match` in the way.

`keep` unfolds and refolds the suffix unchanged. `claim` opens the suffix,
refolds it one cell later, and stores through the cell the old range owned but
the new one no longer does. The refold checks the new endpoint's bounds and
proves the quantified fact over the shorter suffix from the one the unfold
published.

`src/surface/tests/expansion_tests.rs` expands the smart sites of this fixture
and reverifies the result, and checks that `click audit` agrees.

```c filename=resource_field_memory_endpoint.c
struct buffer {
    int32* data;
    int32 capacity;
};

void keep(struct buffer* buffer) {}

void claim(int32* data, int32 capacity, int32 start) {
    data[start] = 7;
}
```

```click
resource suffix_after_prefix(buffer: struct buffer*) {
    field start: int32;
    owns &buffer->data;
    owns buffer->capacity;
    owns buffer->data[start..buffer->capacity];
    fact 0 <= start;
    fact start <= buffer->capacity;
    fact forall (k: int32) {
        start <= k and k < buffer->capacity implies buffer->data[k] == 0
    };
}

resource zero_suffix(data: int32*, capacity: int32) {
    field start: int32;
    owns data[start..capacity];
    fact 0 <= start;
    fact start <= capacity;
    fact forall (k: int32) {
        start <= k and k < capacity implies data[k] == 0
    };
}

verifying "resource_field_memory_endpoint.c";

void keep(struct buffer* buffer) {
    owns suffix: suffix_after_prefix(buffer);
    ensures suffix.start == old(suffix.start);
} by {
    unfold(suffix);
    execute();
    let suffix = fold(suffix_after_prefix(buffer), { start: old(suffix.start) });
    simp();
}

void claim(int32* data, int32 capacity, int32 start) {
    consumes before: zero_suffix(data, capacity);
    produces after: zero_suffix(data, capacity);
    produces data[start..start + 1];
    requires before.start == start;
    requires start < capacity;
    ensures after.start == start + 1;
    ensures data[start] == 7;
} by {
    unfold(before);
    have old(before.start) == start by { simp(); }
    have old(before.start) < capacity by { simp(); }
    have forall (k: int32) {
        old(before.start) + 1 <= k and k < capacity implies data[k] == 0
    } by {
        intro();
        intro();
        extract(old(before.start) + 1 <= k);
        extract(k < capacity);
        apply(int32_increment_strictly_increases(old(before.start), capacity)) using {
            old(before.start) < capacity;
        }
        apply(int32_successor_le_implies_lt(old(before.start), k)) using {
            old(before.start) < old(before.start) + 1;
            old(before.start) + 1 <= k;
        }
        apply(int32_lt_implies_le(old(before.start), k)) using {
            old(before.start) < k;
        }
        instantiate(forall (k: int32) {
            old(before.start) <= k and k < capacity implies data[k] == 0
        }, k) using {
            old(before.start) <= k;
            k < capacity;
        }
        assumption();
    }
    let after = fold(zero_suffix(data, capacity), { start: old(before.start) + 1 });
    execute();
    simp();
}
```

```expect
pass
```
