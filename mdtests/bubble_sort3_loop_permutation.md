# bubble_sort3_loop preserves the three-cell permutation

This checks that the loop-shaped fixed-size bubble sort preserves the
standard-library permutation predicate over the entry-state cells.

```c filename=bubble_sort3_loop_permutation.c
int32 bubble_sort3_loop_permutation(int32 p[3]) {
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
verifying "bubble_sort3_loop_permutation.c";

int32 bubble_sort3_loop_permutation(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures permutation: permutation(p, old(p), 0, 3) by {
        step using {
            fact loadable(p[0..3]);
        }
        step using {
            fact loadable(old(p[0..3]));
        }
        step using {
            fact loadable(old(p[0..3]));
        }
        step using {
            fact loadable(old(p[0..3]));
        }
        step using {
            fact loadable(old(p[0..3]));
        }
        step using {
            fact loadable(old(p[0..3]));
        }
        step using {
            fact loadable(old(p[0..3]));
        }
        if p[(j + 1)] < p[j] {
            step using {
                fact loadable(old(p[0..3]));
            }
            step using {
                fact loadable(old(p[0..3]));
                fact p[(j + 1)] < p[j];
            }
            step using {
                fact loadable(old(p[0..3]));
                fact p[(j + 1)] < p[j];
            }
            step using {
                fact loadable(old(p[0..3]));
                fact *(p + 1) < tmp;
            }
            step using {
                fact loadable(old(p[0..3]));
                fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
            }
            step using {
                fact loadable(old(p[0..3]));
                fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
            }
            if p[(j + 1)] < p[j] {
                step using {
                    fact loadable(old(p[0..3]));
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact *(p + 2) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact p[(j + 1)] < at(statement(0).entry, p[j]);
                }
                if p[(j + 1)] < p[j] {
                    step using {
                        fact loadable(old(p[0..3]));
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, tmp) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *p);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                } else {
                    step using {
                        fact loadable(old(p[0..3]));
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not old(p[(j + 1)]) < old(p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                }
            } else {
                step using {
                    fact loadable(old(p[0..3]));
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + 2) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + 2) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + 2) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + 2) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + i) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact at(statement(0).entry, *(p + 1)) < at(statement(0).entry, tmp);
                    fact not *(p + j) < tmp;
                }
            }
        } else {
            step using {
                fact loadable(old(p[0..3]));
            }
            step using {
                fact loadable(old(p[0..3]));
                fact not p[(j + 1)] < p[j];
            }
            step using {
                fact loadable(old(p[0..3]));
                fact not p[(j + 1)] < p[j];
            }
            step using {
                fact loadable(old(p[0..3]));
                fact not *(p + j) < *p;
            }
            if p[(j + 1)] < p[j] {
                step using {
                    fact loadable(old(p[0..3]));
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact *(p + 2) < tmp;
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not tmp < *p;
                    fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                }
                if p[(j + 1)] < p[j] {
                    step using {
                        fact loadable(old(p[0..3]));
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < p[j];
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *(p + i));
                        fact p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < old(p[j]);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *(p + i));
                        fact p[(j + 1)] < at(statement(0).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < old(p[j]);
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, *(p + i));
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *(p + i));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *(p + i));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < old(p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < old(p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < old(p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not old(p[(j + 1)]) < old(p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not p[(j + 1)] < p[j];
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact at(statement(0).entry, p[(j + 1)]) < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, *(p + 1));
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                    }
                } else {
                    step using {
                        fact loadable(old(p[0..3]));
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + 2)) < at(statement(0).entry, tmp);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not p[(j + 1)] < p[j];
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(12).entry, p[(j + 1)]) < at(statement(12).entry, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, p[(j + 1)]) < at(statement(0).entry, p[j]);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + i)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                    step using {
                        fact loadable(old(p[0..3]));
                        fact not tmp < *p;
                        fact at(statement(0).entry, *(p + j)) < at(statement(0).entry, tmp);
                        fact not at(statement(5).exit, p[(j + 1)]) < at(statement(5).exit, p[j]);
                    }
                }
            } else {
                step using {
                    fact loadable(old(p[0..3]));
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + j) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + j) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not *(p + j) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not *(p + j) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + 2) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + 2) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + 2) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + 2) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not *(p + j) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + i) < *p;
                    fact not *(p + j) < *(p + i);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not p[(j + 1)] < p[j];
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + j) < *p;
                    fact not p[(j + 1)] < p[j];
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + i) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + j) < *(p + 1);
                }
                step using {
                    fact loadable(old(p[0..3]));
                    fact not *(p + 1) < *p;
                    fact not *(p + j) < *(p + 1);
                }
            }
        }
        unfold(permutation);
        simp();
    }
}
```

```expect
pass
```
