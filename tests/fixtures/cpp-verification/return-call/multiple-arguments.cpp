long Mul(long fee, int at_size) noexcept { return fee * long(at_size); }
long Div(long n, int d, bool round_down) noexcept {
    long quot = n / d;
    int mod = int(n % d);
    return quot + ((mod > 0) - (mod && round_down));
}
long EvaluateFee(long fee, int at_size, int divisor, bool round_down) noexcept {
    return Div(Mul(fee, at_size), divisor, round_down);
}
int echo(int value) noexcept { return value; }
int first(int a, int b, int c) noexcept { return a; }
int second(int a, int b, int c) noexcept { return b; }
int third(int a, int b, int c) noexcept { return c; }
int nested_first(int value) noexcept { return first(echo(value), 2, 3); }
int nested_second(int value) noexcept { return second(1, echo(value), 3); }
int nested_third(int value) noexcept { return third(1, 2, echo(value)); }
unsigned echo_unsigned(unsigned value) noexcept { return value; }
unsigned pick_unsigned(unsigned left, unsigned right) noexcept { return right; }
unsigned nested_unsigned(unsigned value, int other) noexcept {
    return pick_unsigned(unsigned(other), echo_unsigned(value));
}
bool echo_bool(bool value) noexcept { return value; }
bool pick_bool(bool left, bool right) noexcept { return right; }
bool nested_bool(bool value, int other) noexcept {
    return pick_bool(bool(other), echo_bool(value));
}
constexpr long kTwo = 2;
int literal_siblings(int value) noexcept {
    return first(echo(value), int(kTwo), int(sizeof(int)));
}
int write_seven(int* slot) noexcept { *slot = 7; return *slot; }
int effectful_inner(int* slot, int saved_value) noexcept {
    return second(saved_value, write_seven(slot), 3);
}
int local_sibling(int* slot, int value) noexcept {
    int saved_value = value;
    return first(saved_value, write_seven(slot), 3);
}
template<bool RoundDown>
long EvaluateTemplate(long fee, int at_size, int divisor) noexcept {
    return Div(Mul(fee, at_size), divisor, RoundDown);
}
long fee_down(long fee, int at_size, int divisor) noexcept {
    return EvaluateTemplate<true>(fee, at_size, divisor);
}
long fee_up(long fee, int at_size, int divisor) noexcept {
    return EvaluateTemplate<false>(fee, at_size, divisor);
}
