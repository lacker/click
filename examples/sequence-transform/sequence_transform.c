void sequence_copy3(int destination[3], int source[3]) {
    destination[0] = source[0];
    destination[1] = source[1];
    destination[2] = source[2];
}

void sequence_concatenate2(
    int destination[4],
    int left[2],
    int right[2]
) {
    destination[0] = left[0];
    destination[1] = left[1];
    destination[2] = right[0];
    destination[3] = right[1];
}

void sequence_reverse3(int values[3]) {
    int first;

    first = values[0];
    values[0] = values[2];
    values[2] = first;
}

int sequence_contains3(int values[3], int target) {
    if (values[0] == target) {
        return 1;
    }
    if (values[1] == target) {
        return 1;
    }
    if (values[2] == target) {
        return 1;
    }
    return 0;
}
