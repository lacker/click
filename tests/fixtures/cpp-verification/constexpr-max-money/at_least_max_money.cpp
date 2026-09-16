#include <cstdint>

typedef int64_t CAmount;
static constexpr CAmount COIN = 100000000;
static constexpr CAmount MAX_MONEY = 21000000 * COIN;

inline bool at_least_max_money(const CAmount& value) {
    return value >= MAX_MONEY;
}

inline bool at_most_max_money(const CAmount& value) {
    return value <= MAX_MONEY;
}
