int set_seven(int& value) noexcept {
    value = 7;
    return value;
}

int call_set_seven(int& value) noexcept {
    set_seven(value);
    return value;
}
