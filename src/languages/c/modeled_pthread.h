/* Click's declaration-only x86-64 Linux user-space pthread projection.
 * These declarations carry no executable or external-contract semantics.
 * The first frozen probe uses null attributes and a null join-result
 * pointer. The mutex projection has the x86-64 glibc size and alignment;
 * its bytes are opaque to C clients of the modeled runtime.
 */
#pragma once
typedef unsigned long pthread_t;
/* An incomplete C0 type deliberately forbids constructing an attribute
 * object; this first profile accepts only a null attributes argument. */
typedef struct __click_pthread_attr pthread_attr_t;
typedef union __click_pthread_mutex {
    char __size[40];
    long __align;
} pthread_mutex_t;
typedef struct __click_pthread_mutexattr pthread_mutexattr_t;

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);
int pthread_mutex_init(pthread_mutex_t *mutex, const pthread_mutexattr_t *attr);
int pthread_mutex_lock(pthread_mutex_t *mutex);
int pthread_mutex_unlock(pthread_mutex_t *mutex);
int pthread_mutex_destroy(pthread_mutex_t *mutex);
