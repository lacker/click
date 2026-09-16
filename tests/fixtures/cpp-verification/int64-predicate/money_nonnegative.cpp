typedef long CAmount;

inline bool money_nonnegative(const CAmount& nValue) {
    return nValue >= 0;
}
