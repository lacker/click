#include "client.h"
#include "registry.h"

static int32_t calls = 100;

int32_t record_beta() {
    static struct counter batches[] = {{0, 'b'}};
    counters[1].value = NEXT_COUNT(counters[1].value);
    calls = NEXT_COUNT(calls);
    batches[0].value = NEXT_COUNT(batches[0].value);
    return calls + batches[0].value;
}

int32_t beta_calls() {
    return calls;
}
