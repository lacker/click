struct RestoreState {
    int* pointer;
    int saved;
};

int stage_restore(int& value) noexcept {
    RestoreState state{&value, value};
    *state.pointer = 7;
    return state.saved;
}
