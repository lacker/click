# Range folds consume lambda values

A fold takes a typed lambda step, including a local alias with lexical captures.
Its step has the signature `fn(Accumulator, Index) -> Accumulator`.

```click
function lambda_total(lo: int32, hi: int32, offset: Integer) -> Integer {
    let step = |acc: Integer, k: int32| -> Integer { acc + to_integer(k) + offset };
    let alias: fn(Integer, int32) -> Integer = step;
    (lo..hi).fold(0, alias)
}

function inline_total(lo: int32, hi: int32, offset: Integer) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) + offset })
}

theorem lambda_and_inline_folds_match(lo: int32, hi: int32, offset: Integer) {
    ensures lambda_total(lo, hi, offset) == inline_total(lo, hi, offset) by {
        unfold(lambda_total(lo, hi, offset));
        unfold(inline_total(lo, hi, offset));
        close();
    }
}

function lambda_integer_total(lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, |acc: Integer, k: Integer| -> Integer { acc + k })
}

function lambda_unsigned_total(lo: uint64, hi: uint64) -> Integer {
    let step = |acc: Integer, k: uint64| -> Integer { acc + to_integer(k) };
    (lo..hi).fold(0, step)
}

function lambda_machine_total(lo: int32, hi: int32) -> int32 {
    (lo..hi).fold(0, |acc: int32, k: int32| -> int32 { acc })
}

function lambda_capture_shadow(lo: int32, hi: int32, __click_fold_0: Integer) -> Integer {
    let step = |acc: Integer, k: int32| -> Integer { acc + __click_fold_0 };
    let __click_fold_0: Integer = 100;
    (lo..hi).fold(0, step)
}

theorem lambda_fold_carriers(lo: Integer, hi: Integer, a: uint64, b: uint64, c: int32, d: int32) {
    ensures lambda_integer_total(lo, hi) == (lo..hi).fold(0, |acc, k| { acc + k }) by {
        unfold(lambda_integer_total(lo, hi));
        close();
    }
    ensures lambda_unsigned_total(a, b) == (a..b).fold(0, |acc, k| { acc + to_integer(k) }) by {
        unfold(lambda_unsigned_total(a, b));
        close();
    }
    ensures lambda_machine_total(c, d) == (c..d).fold(0, |acc, k| { acc }) by {
        unfold(lambda_machine_total(c, d));
        close();
    }
    ensures lambda_capture_shadow(c, d, 5) == (c..d).fold(to_integer(0), |acc, k| { acc + 5 }) by {
        unfold(lambda_capture_shadow(c, d, 5));
        close();
    }
}

theorem lambda_fold_append(lo: int32, hi: int32, offset: Integer) {
    requires lo <= hi;
    requires hi < 2147483647;
    ensures lambda_total(lo, hi + 1, offset) == lambda_total(lo, hi, offset) + to_integer(hi) + offset by {
        unfold(lambda_total(lo, hi + 1, offset));
        close();
    }
}

```

```expect
pass
```
