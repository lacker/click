# bubble_sort3_loop sorts three cells

This checks the loop-shaped fixed-size sorting target: a concrete two-loop
bubble sort over three cells should leave `p[0..3]` nondecreasing.

```c filename=bubble_sort3_loop.c
int32 bubble_sort3_loop(int32 p[3]) {
    int32 i;
    int32 j;
    int32 tmp;
    i = 0;
    while (i < 3) {
        j = 0;
        while (j < 2) {
            if (p[j + 1] < p[j]) {
                tmp = p[j];
                p[j] = p[j + 1];
                p[j + 1] = tmp;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "bubble_sort3_loop.c";

predicate sorted(p: int32[], n: int32) {
    sorted_range(p, 0, n)
}

predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

int32 bubble_sort3_loop(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3) by {
        step() using {
            loadable(p[0..3]);
        }
        step() using {
            loadable(old(p[0..3]));
        }
        step() using {
            loadable(old(p[0..3]));
        }
        step() using {
            loadable(old(p[0..3]));
        }
        step() using {
            loadable(old(p[0..3]));
        }
        step() using {
            loadable(old(p[0..3]));
        }
        step() using {
            loadable(old(p[0..3]));
        }
        if at(function.entry, p[1]) < at(function.entry, *p) {
            step() using {
                loadable(old(p[0..3]));
            }
            step() using {
                loadable(old(p[0..3]));
                at(function.entry, p[1]) < at(function.entry, *p);
            }
            step() using {
                loadable(old(p[0..3]));
                at(function.entry, p[1]) < at(function.entry, *p);
            }
            step() using {
                loadable(old(p[0..3]));
                at(function.entry, p[1]) < at(function.entry, *p);
            }
            step() using {
                loadable(old(p[0..3]));
                at(function.entry, p[1]) < at(function.entry, *p);
            }
            step() using {
                loadable(old(p[0..3]));
                at(function.entry, p[1]) < at(function.entry, *p);
            }
            if at(function.entry, p[2]) < at(function.entry, *p) {
                step() using {
                    loadable(old(p[0..3]));
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    at(function.entry, p[2]) < at(function.entry, *p);
                }
                if at(function.entry, p[2]) < at(function.entry, p[1]) {
                    step() using {
                        loadable(old(p[0..3]));
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                    }
                } else {
                    step() using {
                        loadable(old(p[0..3]));
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        at(function.entry, p[1]) < at(function.entry, *p);
                        at(function.entry, p[2]) < at(function.entry, *p);
                        not old(p[2]) < old(p[1]);
                    }
                }
            } else {
                step() using {
                    loadable(old(p[0..3]));
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
                step() using {
                    loadable(old(p[0..3]));
                    at(function.entry, p[1]) < at(function.entry, *p);
                    not p[2] < tmp;
                }
            }
        } else {
            step() using {
                loadable(old(p[0..3]));
            }
            step() using {
                loadable(old(p[0..3]));
                not p[1] < *p;
            }
            step() using {
                loadable(old(p[0..3]));
                not p[1] < *p;
            }
            step() using {
                loadable(old(p[0..3]));
                not p[1] < *p;
            }
            if at(function.entry, p[2]) < at(function.entry, p[1]) {
                step() using {
                    loadable(old(p[0..3]));
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                step() using {
                    loadable(old(p[0..3]));
                    not tmp < *p;
                    at(function.entry, p[2]) < at(function.entry, p[1]);
                }
                if at(function.entry, p[2]) < at(function.entry, *p) {
                    step() using {
                        loadable(old(p[0..3]));
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not old(p[1]) < tmp;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        at(function.entry, p[2]) < at(function.entry, *p);
                    }
                } else {
                    step() using {
                        loadable(old(p[0..3]));
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                    step() using {
                        loadable(old(p[0..3]));
                        not tmp < *p;
                        at(function.entry, p[2]) < at(function.entry, p[1]);
                        not old(p[2]) < *p;
                    }
                }
            } else {
                step() using {
                    loadable(old(p[0..3]));
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
                step() using {
                    loadable(old(p[0..3]));
                    not p[1] < *p;
                    not p[2] < p[1];
                }
            }
        }
        unfold(sorted);
        unfold(sorted_range);
    }
}
```

```expect
pass
```
