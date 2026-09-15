int bump_pointer(int* pointer) noexcept {
    *pointer = *pointer + 1;
    return *pointer;
}

int bump_reference(int& value) noexcept {
    int result = bump_pointer(&value);
    return result;
}
