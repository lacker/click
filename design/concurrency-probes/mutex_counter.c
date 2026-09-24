#include <pthread.h>
#include <stddef.h>

struct mutex_counter {
    pthread_mutex_t mutex;
    unsigned int value;
};

void *increment_counter(void *argument) {
    struct mutex_counter *counter = argument;
    (void)pthread_mutex_lock(&counter->mutex);
    counter->value = counter->value + 1u;
    (void)pthread_mutex_unlock(&counter->mutex);
    return NULL;
}

int increment_twice(struct mutex_counter *counter) {
    pthread_t first;
    pthread_t second;

    counter->value = 0u;
    if (pthread_mutex_init(&counter->mutex, NULL) != 0) return 0;
    if (pthread_create(&first, NULL, increment_counter, counter) != 0) {
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }
    if (pthread_create(&second, NULL, increment_counter, counter) != 0) {
        (void)pthread_join(first, NULL);
        (void)pthread_mutex_destroy(&counter->mutex);
        return 0;
    }

    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    (void)pthread_mutex_destroy(&counter->mutex);
    return 1;
}
