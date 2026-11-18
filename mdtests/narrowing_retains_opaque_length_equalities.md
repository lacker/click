# Narrowed opaque lengths retain their selected equality

A stated equality for a formatting length rewrites below both a narrowing cast
and a sum's low-word conversion.

```click
import click::c::stdio;

theorem narrowed_length(n: uint64) {
    requires stdio::padded_length(n, 3u64) == 3u64;
    ensures (stdio::padded_length(n, 3u64) as int32) == 3 by {
        rewrite(stdio::padded_length(n, 3u64), 3u64);
        normalize();
    }
}

theorem narrowed_length_sum(n: uint64) {
    requires stdio::padded_length(n, 3u64) == 3u64;
    ensures (1u64 + stdio::padded_length(n, 3u64)) as int32 == 4 by {
        rewrite(stdio::padded_length(n, 3u64), 3u64);
        normalize();
    }
}

theorem narrowed_length_result(n: uint64, result: int32) {
    requires stdio::padded_length(n, 3u64) == 3u64;
    requires result == (1u64 + stdio::padded_length(n, 3u64)) as int32;
    ensures result == 4 by {
        have (1u64 + stdio::padded_length(n, 3u64)) as int32 == 4 by {
            rewrite(stdio::padded_length(n, 3u64), 3u64);
            normalize();
        }
        solve() using {
            result == (1u64 + stdio::padded_length(n, 3u64)) as int32;
            (1u64 + stdio::padded_length(n, 3u64)) as int32 == 4;
        };
    }
}

theorem narrowed_length_result_from_listed_equalities(n: uint64, result: int32) {
    requires stdio::padded_length(n, 3u64) == 3u64;
    requires result == (1u64 + stdio::padded_length(n, 3u64)) as int32;
    ensures result == 4 by {
        solve() using {
            result == (1u64 + stdio::padded_length(n, 3u64)) as int32;
            stdio::padded_length(n, 3u64) == 3u64;
        };
    }
}

```

```expect
pass
```
