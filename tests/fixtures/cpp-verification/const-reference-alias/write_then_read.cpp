int write_then_read(int& writable, const int& readable) noexcept {
    writable = 7;
    return readable;
}
