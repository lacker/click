#include "registry.h"
#include "client.h"

static int32_t calls = 0;

int32_t record_alpha() {
    static int32_t batches[][2] = {{0, 7}};
#if REGISTRY_ENABLED
    counters[0].value = NEXT_COUNT(counters[0].value);
    calls = NEXT_COUNT(calls);
    batches[0][0] = NEXT_COUNT(batches[0][0]);
#endif
    return calls + batches[0][0];
}

int32_t alpha_calls() {
    return calls;
}
