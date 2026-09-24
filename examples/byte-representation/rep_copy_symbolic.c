void *malloc(unsigned long size);
void free(void *ptr);
void *memcpy(void *dest, const void *src, unsigned long n);

struct record {
    unsigned int tag;
    int *target;
};

int g(unsigned int tag, int *p, int **restored) {
    struct record *src = malloc(sizeof(struct record));
    if (src == 0) {
        return -1;
    }
    unsigned char *buf = malloc(16);
    if (buf == 0) {
        free(src);
        return -1;
    }
    struct record *dst = malloc(sizeof(struct record));
    if (dst == 0) {
        free(src);
        free(buf);
        return -1;
    }
    src->tag = tag;
    src->target = p;
    memcpy(buf, (unsigned char *)(void *)src, sizeof(struct record));
    memcpy((unsigned char *)(void *)dst, buf, sizeof(struct record));
    *restored = dst->target;
    int out = dst->tag + *dst->target;
    free(src);
    free(buf);
    free(dst);
    return out;
}
