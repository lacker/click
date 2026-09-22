# A stack job backs ordinary borrowed contracts without ownership annotations

The caller initializes a local struct and lends its fields through the existing
`views` clauses. A nested call reborrows the same fields. Both calls close their
loans before the caller writes the job again and leaves its scope.

```c filename=local_job.c
struct local_job {
    int first;
    int second;
};

int read_local_job(struct local_job *job) {
    return job->first;
}

int relay_local_job(struct local_job *job) {
    return read_local_job(job);
}

int use_local_job(void) {
    struct local_job job = {7, 11};
    int result = relay_local_job(&job);
    job.first = 19;
    return result;
}
```

```click
verifying "local_job.c";

int read_local_job(struct local_job *job) {
    views job->first;
    views job->second;
    ensures result == job->first;
} by {
    execute();
    simp();
}

int relay_local_job(struct local_job *job) {
    views job->first;
    views job->second;
    ensures result == job->first;
} by {
    execute();
    simp();
}

int use_local_job() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
