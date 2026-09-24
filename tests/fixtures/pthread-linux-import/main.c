#include <pthread.h>
#include <stddef.h>

struct range_job {
    int *output;
    int begin;
    int end;
    int value;
};

void *fill_range(void *argument) {
    struct range_job *job = argument;
    for (int index = job->begin; index < job->end; ++index) {
        job->output[index] = job->value;
    }
    return NULL;
}

int fill_parallel(int output[4]) {
    pthread_t first;
    pthread_t second;
    struct range_job first_job = {output, 0, 2, 11};
    struct range_job second_job = {output, 2, 4, 22};

    for (int index = 0; index < 4; ++index) {
        output[index] = 0;
    }

    if (pthread_create(&first, NULL, fill_range, &first_job) != 0) {
        return 0;
    }
    if (pthread_create(&second, NULL, fill_range, &second_job) != 0) {
        (void)pthread_join(first, NULL);
        return 0;
    }

    (void)pthread_join(first, NULL);
    (void)pthread_join(second, NULL);
    return 1;
}
