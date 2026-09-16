#include <cstdint>

typedef int64_t CAmount;
static constexpr CAmount COIN = 100000000;

inline bool at_least_one_coin(const CAmount& value) {
    return value >= COIN;
}
