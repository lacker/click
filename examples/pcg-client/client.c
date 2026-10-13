/* A client of the unchanged pcg-c-basic library: seed the global generator,
 * draw its first two outputs, then reseed and check the sequence restarts. */
#include "../pcg-basic/pcg_basic.h"

int first_outputs_repeat(void)
{
    pcg32_srandom(42u, 54u);
    uint32_t first = pcg32_random();
    uint32_t second = pcg32_random();
    pcg32_srandom(42u, 54u);
    uint32_t again = pcg32_random();
    return first == 0xa15c02b7u && second == 0x7b47f409u && again == first;
}
