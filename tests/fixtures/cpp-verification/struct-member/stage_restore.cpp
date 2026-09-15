struct RestoreState {
    int* pointer;
    int saved;
};

int stage_restore(RestoreState& state, int& value) noexcept {
    state.pointer = &value;
    state.saved = value;
    *state.pointer = 7;
    return state.saved;
}
