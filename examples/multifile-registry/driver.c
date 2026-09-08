#include "client.h"
#include "registry.h"

int32_t registry_run() {
    int32_t first = record_alpha();
    int32_t second = record_alpha();
    int32_t third = record_beta();
    int32_t alpha_total = alpha_calls();
    int32_t beta_total = beta_calls();
    return first + second + third + alpha_total + beta_total
        + weights[0][1] + weights[1][1];
}
