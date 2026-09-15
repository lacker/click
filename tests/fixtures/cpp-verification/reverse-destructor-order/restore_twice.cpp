struct Restore {
    int* p;
    int saved;

    explicit Restore(int* slot) noexcept : p(slot), saved(*slot) {
        *p = 7;
    }

    ~Restore() noexcept {
        *p = saved;
    }
};

int restore_twice(bool early, int& value) noexcept {
    Restore first(&value);
    Restore second(&value);
    if (early) {
        return value;
    }
    value = 9;
    return value;
}
