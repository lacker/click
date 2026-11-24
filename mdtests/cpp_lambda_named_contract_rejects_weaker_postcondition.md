# A C++ lambda must meet the named contract of the pointer it is passed for

The lambda's contract only says its result is at least its argument, which
does not give `Doubling`, so `caller` cannot pass it to `apply`.

```cpp filename=lambda.cpp function=caller profile=normal_only
int apply(int (*f)(int) noexcept, int x) noexcept { return f(x); }
int caller(int x) noexcept {
    return apply([](int y) noexcept { return y + y; }, x);
}
```

```click
verifying "lambda.cpp";
contract int Doubling(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int apply(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int caller::(lambda#0)(int y) {
    requires 0 <= y and y <= 1000;
    ensures result >= y;
}
theorem proposed_lambda_doubles() {
    ensures Doubling(&caller::(lambda#0)) by { unfold(Doubling(&caller::(lambda#0))); close(); }
}
int caller(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
```

```expect
fail: contract-refinement proof does not establish `Doubling(&caller::(lambda#0))`
```
