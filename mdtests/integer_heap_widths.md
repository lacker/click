# Heap allocations retain non-scalar integer widths

Runtime heap cells use the declared integer width for allocation, indexing,
initialization, and reclamation.

```c filename=integer_heap_widths.c
int16_t malloc_int16_array() {
    int16_t* data = malloc(2 * sizeof(int16_t));
    if (data == 0) {
        return 0;
    }
    data[0] = 3;
    data[1] = 5;
    int16_t result = data[1];
    free(data);
    return result;
}

uint16_t malloc_uint16_array() {
    uint16_t* data = malloc(2 * sizeof(uint16_t));
    if (data == 0) {
        return 0;
    }
    data[0] = 7;
    data[1] = 11;
    uint16_t result = data[1];
    free(data);
    return result;
}

uint32_t malloc_uint32_array() {
    uint32_t* data = malloc(2 * sizeof(uint32_t));
    if (data == 0) {
        return 0;
    }
    data[0] = 13U;
    data[1] = 17U;
    uint32_t result = data[1];
    free(data);
    return result;
}

int64_t malloc_int64_array() {
    int64_t* data = malloc(2 * sizeof(int64_t));
    if (data == 0) {
        return 0;
    }
    data[0] = -19LL;
    data[1] = 23LL;
    int64_t result = data[1];
    free(data);
    return result;
}

uint64_t calloc_uint64_array() {
    uint64_t* data = calloc(2, sizeof(uint64_t));
    if (data == 0) {
        return 0;
    }
    uint64_t result = data[1];
    free(data);
    return result;
}

uint16_t calloc_uint16_array_with_size_t(size_t count) {
    uint16_t* data = calloc(count, sizeof(uint16_t));
    if (data == 0) {
        return 0;
    }
    uint16_t result = data[1];
    free(data);
    return result;
}

uint64_t malloc_uint64_array_with_size_t(size_t count) {
    uint64_t* data = malloc(count * sizeof(uint64_t));
    if (data == 0) {
        return 0;
    }
    data[1] = 29ULL;
    uint64_t result = data[1];
    free(data);
    return result;
}

uint64_t realloc_uint64_array_with_size_t(size_t count) {
    uint64_t* data = malloc(2 * sizeof(uint64_t));
    if (data == 0) {
        return 0;
    }
    data[0] = 37ULL;
    uint64_t* resized = realloc(data, count * sizeof(uint64_t));
    if (resized == 0) {
        free(data);
        return 0;
    }
    data = resized;
    uint64_t result = data[0];
    free(data);
    return result;
}
```

```click
verifying "integer_heap_widths.c";

int16_t malloc_int16_array() {
    ensures result == 0 or result == 5 by auto;
}

uint16_t malloc_uint16_array() {
    ensures result == 0 or result == 11 by auto;
}

uint32_t malloc_uint32_array() {
    ensures result == 0 or result == 17 by auto;
}

int64_t malloc_int64_array() {
    ensures result == 0 or result == 23 by auto;
}

uint64_t calloc_uint64_array() {
    ensures result == 0;
}

uint16_t calloc_uint16_array_with_size_t(size_t count) {
    requires count == 2;
    ensures result == 0;
}

uint64_t malloc_uint64_array_with_size_t(size_t count) {
    requires count == 2;
    ensures result == 0 or result == 29 by auto;
}

uint64_t realloc_uint64_array_with_size_t(size_t count) {
    requires count == 3;
    ensures result == 0 or result == 37 by auto;
}
```

```expect
pass
```
