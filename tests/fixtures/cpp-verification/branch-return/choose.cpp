int choose(bool early, int& value) noexcept {
    value = 7;
    if (early) {
        return value;
    }
    value = 9;
    return value;
}
