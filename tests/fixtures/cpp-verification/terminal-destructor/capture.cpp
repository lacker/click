struct RestoreState {
    int* pointer;
    int saved;

    explicit RestoreState(int* slot) noexcept
        : pointer(slot), saved(*slot) {
        *pointer = 7;
    }

    ~RestoreState() noexcept {
        *pointer = saved;
    }
};

int capture(int& value) noexcept {
    RestoreState state(&value);
    return value;
}
