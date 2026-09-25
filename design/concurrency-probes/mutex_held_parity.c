#include <pthread.h>
#include <stddef.h>

struct parity_mutex {
    pthread_mutex_t mutex;
};

int alternate_mutex(struct parity_mutex *object, int n) {
    if (pthread_mutex_init(&object->mutex, NULL) != 0) return 0;

    int i = 0;
    while (i < n) {
        if (i % 2 == 0) {
            (void)pthread_mutex_lock(&object->mutex);
        } else {
            (void)pthread_mutex_unlock(&object->mutex);
        }
        i++;
    }

    if (i % 2 != 0) (void)pthread_mutex_unlock(&object->mutex);
    (void)pthread_mutex_destroy(&object->mutex);
    return 1;
}
