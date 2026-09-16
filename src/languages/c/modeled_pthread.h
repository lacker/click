/* Click's declaration-only x86-64 Linux user-space pthread projection.
 * These declarations carry no executable or external-contract semantics.
 * The first frozen probe uses null attributes and a null join-result
 * pointer; other pthread operations remain outside this projection.
 */
#pragma once
typedef unsigned long pthread_t;
/* An incomplete C0 type deliberately forbids constructing an attribute
 * object; this first profile accepts only a null attributes argument. */
typedef struct __click_pthread_attr pthread_attr_t;

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);
