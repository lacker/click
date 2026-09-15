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

int overlap_restore(bool early, int& value) noexcept {
    Restore outer(&value);
    {
        Restore inner(&value);
        if (early) {
            return value;
        }
        value = 11;
    }
    int observed = value;
    return observed;
}
