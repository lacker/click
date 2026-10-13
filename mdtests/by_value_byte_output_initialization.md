# A by-value output descriptor selects the frozen entry byte pointer

Explicit initialization covers all four bytes. The helper's private descriptor
copy supplies the output pointer; ownership alone supplies no initialized values.

```c filename=span_output.c
struct byte_span { unsigned char* data; unsigned int count; };
void fill_span(struct byte_span out) {
    out.data[0] = 120;
    out.data[1] = 86;
    out.data[2] = 52;
    out.data[3] = 18;
}
unsigned int span_word(void) {
    unsigned int value;
    struct byte_span out;
    out.data = (unsigned char*)(void*)&value;
    out.count = 4;
    fill_span(out);
    return value;
}
```

```click
verifying "span_output.c";
void fill_span(struct byte_span out) {
    owns out.data[0..4];
    ensures initialized(out.data[0..4]);
} by { execute(); simp(); }
uint32 span_word() { ensures result == result; } by { execute(); simp(); }
```

```expect
pass
```
