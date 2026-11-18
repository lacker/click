spec enum WriteAttempt {
    Accepted(List<uint8>),
    Failed(List<uint8>),
}

abstract resource stream(file: void*) {
    field write_history: List<WriteAttempt>;
}
