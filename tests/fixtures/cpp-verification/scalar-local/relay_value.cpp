int read_value(int& value) noexcept {
    return value;
}

int relay_value(int& value) noexcept {
    int captured = read_value(value);
    int relayed = captured;
    relayed = relayed + 1;
    return relayed;
}
