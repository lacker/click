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

int scoped_restore(bool early, int& value) noexcept {
    {
        Restore guard(&value);
        if (early) {
            return value;
        }
        value = 9;
    }
    return value;
}
