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

int sibling_restore(bool first_early, bool second_early, int& value) noexcept {
    {
        Restore guard(&value);
        if (first_early) {
            return value;
        }
        value = 9;
    }
    {
        Restore guard(&value);
        if (second_early) {
            return value;
        }
        value = 11;
    }
    return value;
}
