#ifndef REGISTRY_H
#define REGISTRY_H
#include <stdint.h>
#define REGISTRY_ENABLED 1
#define NEXT_COUNT(x) ((x) + 1)

struct counter {
    int32_t value;
    uint8_t name;
};
extern struct counter counters[3];
extern const int32_t weights[][2];
int32_t record_alpha();
int32_t record_beta();
int32_t alpha_calls();
int32_t beta_calls();
int32_t registry_run();
#endif
