# A cyclic, two-successor graph search

The C is the graph search from `design/dfs-gaps/branching_graph_dfs.md`, unchanged.
Both successor arrays are bounded and read-only; `visited` is mutable. The
number of unmarked cells ranks both recursive calls, including the right call
after the left call may have marked additional nodes. The recursive contract
also preserves every previously marked node. A nonzero result supplies a
finite left/right path in the entry graph and proves the target was in bounds
and unmarked at entry. Both recursive success branches construct and frame
their witnesses. A zero return leaves the root marked and every newly marked
node closed under both successor edges. The target cell is unchanged. Together
these imply that, from an all-unmarked entry state, zero means no finite path
reaches the target. The recursive calls retain the more general contract so
marks created by the left call are allowed at the right call's entry.

```c filename=branching_graph_dfs.c
int32 dfs(int32 *left, int32 *right, int32 *visited,
          int32 n, int32 cur, int32 to) {
    if (visited[cur] != 0) return 0;
    if (cur == to) return 1;
    visited[cur] = 1;
    if (dfs(left, right, visited, n, left[cur], to)) return 1;
    return dfs(left, right, visited, n, right[cur], to);
}
```

```click
verifying "branching_graph_dfs.c";

import "unmarked_count_lemmas.click";
import "branching_graph_paths.click";

resource bounded_successors(left: int32*, right: int32*, n: int32) {
    views left[0..n];
    views right[0..n];
    fact forall (k: int32) {
        0 <= k and k < n implies 0 <= left[k] and left[k] < n
    };
    fact forall (k: int32) {
        0 <= k and k < n implies 0 <= right[k] and right[k] < n
    };
}

theorem marked_transitive(a: int32[], b: int32[], c: int32[], n: int32) {
    requires forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies b[k] != 0 };
    requires forall (k: int32) { 0 <= k and k < n and b[k] != 0 implies c[k] != 0 };
    ensures forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies c[k] != 0 } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        extract(a[k] != 0);
        instantiate(forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies b[k] != 0 }, k) using { 0 <= k; k < n; a[k] != 0; }
        instantiate(forall (k: int32) { 0 <= k and k < n and b[k] != 0 implies c[k] != 0 }, k) using { 0 <= k; k < n; b[k] != 0; }
        assumption();
    }
}

int32 dfs(int32 *left, int32 *right, int32 *visited,
          int32 n, int32 cur, int32 to) {
    decreases unmarked(visited, 0, n);
    requires 0 <= cur;
    requires cur < n;
    requires n <= 1073741823;
    views bounded_successors(left, right, n);
    owns visited[0..n];
    requires separate(memory(left[0..n]), memory(visited[0..n]));
    requires separate(memory(right[0..n]), memory(visited[0..n]));
    ensures unmarked(visited, 0, n) <= old(unmarked(visited, 0, n));
    ensures result != 0 implies exists (path: Path) {
        walk(old(left), old(right), cur, path) == to
    };
    ensures result != 0 implies 0 <= to and to < n and old(visited[to]) == 0;
    ensures 0 <= to and to < n implies visited[to] == old(visited[to]);
    ensures result == 0 implies (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to };
    ensures result == 0 implies visited[cur] != 0;
    ensures result == 0 implies forall (k: int32) {
        0 <= k and k < n and old(visited[k]) == 0 and visited[k] != 0 implies
            visited[old(left[k])] != 0 and visited[old(right[k])] != 0
    };
    ensures forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
    };
} by {
    observe(bounded_successors(left, right, n));
    have forall (k: int32) {
        0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n
    } by { assumption(); }
    have forall (k: int32) {
        0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n
    } by { assumption(); }

    branch {
        then {
            have (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to } by {
                intro();
                instantiate(forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }, cur) using { 0 <= cur; cur < n; }
                contradiction(visited[cur] != 0);
            }

            have forall (k: int32) {
                0 <= k and k < n and old(visited[k]) == 0 and visited[k] != 0 implies
                    visited[old(left[k])] != 0 and visited[old(right[k])] != 0
            } by {
                intro(); intro();
                extract(old(visited[k]) == 0); extract(visited[k] != 0);
                contradiction(visited[k] != 0);
            }

            have forall (k: int32) {
                0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
            } by { intro(); intro(); simp(); }
            have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
                intro(); normalize();
            }
            step();
            have result == 0 implies (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to } by { intro(); assumption(); }
            simp();
        }
        else {}
    }
    branch {
        then {
            have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
                witness(path = Path::Here);
                unfold(walk(old(left), old(right), cur, Path::Here));
                simp();
            }
            have 0 <= to and to < n and old(visited[to]) == 0 by {
                rewrite(to == cur);
                simp();
            }
            have forall (k: int32) {
                0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
            } by { intro(); intro(); simp(); }
            have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
                intro(); normalize();
            }
            step();
            simp();
        }
        else {}
    }
    mark before_mark;
    step();
    have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
        intro();
        extract(0 <= to); extract(to < n);
        transport(old(visited[to]) == at(before_mark, visited[to]), old(visited[to]) == visited[to]) using {
            old(visited[to]) == at(before_mark, visited[to]);
            0 <= to; to < n; cur != to;
        };
        simp();
    }

    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
    } by {
        intro();
        intro();
        extract(0 <= k);
        extract(k < n);
        extract(old(visited[k]) != 0);
        if k == cur {
            rewrite(k == cur);
            simp();
        } else {
            transport(old(visited[k]) == at(before_mark, visited[k]), old(visited[k]) == visited[k]) using {
                old(visited[k]) == at(before_mark, visited[k]);
                0 <= k; k < n; k != cur;
            };
            simp() using { old(visited[k]) != 0; old(visited[k]) == visited[k]; }
        }
    }

    have forall (k: int32) {
        0 <= k and k < cur implies at(before_mark, visited[k]) == visited[k]
    } by {
        intro();
        intro();
        extract(k < cur);
        have k != cur by {
            apply(int32_lt_implies_neq(k, cur)) using { k < cur; }
            assumption();
        }
        transport(
            at(before_mark, visited[k]) == at(before_mark, visited[k]),
            at(before_mark, visited[k]) == visited[k]
        ) using {
            at(before_mark, visited[k]) == at(before_mark, visited[k]);
            k != cur;
        };
        assumption();
    }
    have forall (k: int32) {
        cur < k and k < n implies at(before_mark, visited[k]) == visited[k]
    } by {
        intro();
        intro();
        extract(cur < k);
        have cur != k by {
            apply(int32_lt_implies_neq(cur, k)) using { cur < k; }
            assumption();
        }
        transport(
            at(before_mark, visited[k]) == at(before_mark, visited[k]),
            at(before_mark, visited[k]) == visited[k]
        ) using {
            at(before_mark, visited[k]) == at(before_mark, visited[k]);
            cur != k;
        };
        assumption();
    }
    have visited[cur] != 0 by { simp(); }
    have viewable(visited[0..n]) by { simp(); }
    apply(unmarked_point_update(at(before_mark, visited), visited, 0, n, n, cur));
    apply(unmarked_nonnegative(visited, 0, n, n));
    have unmarked(visited, 0, n) < unmarked(at(before_mark, visited), 0, n) by {
        arithmetic() using {
            unmarked(visited, 0, n) == unmarked(at(before_mark, visited), 0, n) - 1;
        }
    }
    have unmarked(at(before_mark, visited), 0, n) == old(unmarked(visited, 0, n)) by {
        simp();
    }
    have unmarked(visited, 0, n) < old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n) < unmarked(at(before_mark, visited), 0, n);
            unmarked(at(before_mark, visited), 0, n) == old(unmarked(visited, 0, n));
        }
    }
    observe(bounded_successors(left, right, n));
    have 0 <= left[cur] and left[cur] < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= left[k] and left[k] < n
        }, cur) using { 0 <= cur; cur < n; }
        assumption();
    }
    mark after_mark;
    have forall (k: int32) {
        0 <= k and k < n and k != cur implies old(visited[k]) == at(after_mark, visited[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n); extract(k != cur);
        transport(old(visited[k]) == at(before_mark, visited[k]), old(visited[k]) == at(after_mark, visited[k])) using {
            old(visited[k]) == at(before_mark, visited[k]);
            0 <= k; k < n; k != cur;
        };
        assumption();
    }

    have forall (k: int32) {
        0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        transport(old(left[k]) == old(left[k]), old(left[k]) == at(after_mark, left[k])) using {
            old(left[k]) == old(left[k]);
            0 <= k; k < n;
            separate(memory(left[0..n]), memory(visited[0..n]));
        };
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < n implies old(right[k]) == at(after_mark, right[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        transport(old(right[k]) == old(right[k]), old(right[k]) == at(after_mark, right[k])) using {
            old(right[k]) == old(right[k]);
            0 <= k; k < n;
            separate(memory(right[0..n]), memory(visited[0..n]));
        };
        assumption();
    }

    let left_result = step(dfs(left, right, visited, n, left[cur], to), {});
    have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
        intro();
        extract(visited[to] == at(after_mark, visited[to]));
        extract(at(after_mark, visited[to]) == old(visited[to]));
        simp();
    }
    have visited[cur] != 0 by {
        instantiate(forall (k: int32) {
            0 <= k and k < n and at(after_mark, visited[k]) != 0 implies visited[k] != 0
        }, cur) using { 0 <= cur; cur < n; at(after_mark, visited[cur]) != 0; }
        assumption();
    }

    have forall (k: int32) {
        0 <= k and k < n and at(after_mark, visited[k]) != 0 implies visited[k] != 0
    } by { assumption(); }
    apply(marked_transitive(old(visited), at(after_mark, visited), visited, n));

    have unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n) by {
        simp();
    }
    have unmarked(at(after_mark, visited), 0, n)
        == unmarked(at(before_mark, visited), 0, n) - 1 by {
        simp();
    }
    have unmarked(visited, 0, n) <= old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n);
            unmarked(at(after_mark, visited), 0, n)
                == unmarked(at(before_mark, visited), 0, n) - 1;
            unmarked(at(before_mark, visited), 0, n)
                == old(unmarked(visited, 0, n));
        }
    }
    branch {
        then {
            have exists (path: Path) {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), path) == to
            } by { simp(); }
            let (rest: Path) satisfy {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), rest) == to
            };
            have walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)) == to by {
                unfold(walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)));
                assumption();
            }
            apply(walk_frame(old(left), old(right), at(after_mark, left), at(after_mark, right), n, cur, Path::Left(rest)));
            have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
                witness(path = Path::Left(rest));
                simp() using {
                    walk(old(left), old(right), cur, Path::Left(rest)) == walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest));
                    walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)) == to;
                }
            }
            have 0 <= to and to < n and at(after_mark, visited[to]) == 0 by {
                extract(0 <= to and to < n and at(after_mark, visited[to]) == 0);
                assumption();
            }
            have old(visited[to]) == 0 by {
                if old(visited[to]) != 0 {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and old(visited[k]) != 0 implies at(after_mark, visited[k]) != 0
                    }, to) using { 0 <= to; to < n; old(visited[to]) != 0; }
                    contradiction(at(after_mark, visited[to]) == 0);
                } else { simp(); }
            }
            step();
            simp();
        }
        else {}
    }
    observe(bounded_successors(left, right, n));
    have viewable(visited[0..n]) by { simp(); }
    apply(unmarked_nonnegative(visited, 0, n, n));
    have unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n) by {
        simp();
    }
    have unmarked(at(after_mark, visited), 0, n)
        == unmarked(at(before_mark, visited), 0, n) - 1 by {
        simp();
    }
    have unmarked(visited, 0, n) < old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n);
            unmarked(at(after_mark, visited), 0, n)
                == unmarked(at(before_mark, visited), 0, n) - 1;
            unmarked(at(before_mark, visited), 0, n)
                == old(unmarked(visited, 0, n));
        }
    }
    have 0 <= right[cur] and right[cur] < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= right[k] and right[k] < n
        }, cur) using { 0 <= cur; cur < n; }
        assumption();
    }
    mark before_right;
    have forall (k: int32) {
        0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
            at(before_right, visited[at(after_mark, left[k])]) != 0 and at(before_right, visited[at(after_mark, right[k])]) != 0
    } by {
        extract(forall (k: int32) {
            0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
                at(before_right, visited[at(after_mark, left[k])]) != 0 and at(before_right, visited[at(after_mark, right[k])]) != 0
        });
        assumption();
    }
    have at(after_mark, left[cur]) == old(left[cur]) by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
        }, cur) using { 0 <= cur; cur < n; }
        simp();
    }
    have left_result == 0 implies at(before_right, visited[at(after_mark, left[cur])]) != 0 by {
        rewrite(at(after_mark, left[cur]) == old(left[cur])); assumption();
    }
    have at(before_right, visited[at(after_mark, left[cur])]) != 0 by {
        extract(at(before_right, visited[at(after_mark, left[cur])]) != 0);
        assumption();
    }

    have forall (k: int32) {
        0 <= k and k < n implies old(left[k]) == at(before_right, left[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        instantiate(forall (k: int32) {
            0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
        }, k) using { 0 <= k; k < n; }
        transport(old(left[k]) == at(after_mark, left[k]), old(left[k]) == at(before_right, left[k])) using {
            old(left[k]) == at(after_mark, left[k]);
            0 <= k; k < n;
            separate(memory(left[0..n]), memory(visited[0..n]));
        };
        assumption();
    }
    have forall (k: int32) {
        0 <= k and k < n implies old(right[k]) == at(before_right, right[k])
    } by {
        intro(); intro();
        extract(0 <= k); extract(k < n);
        instantiate(forall (k: int32) {
            0 <= k and k < n implies old(right[k]) == at(after_mark, right[k])
        }, k) using { 0 <= k; k < n; }
        transport(old(right[k]) == at(after_mark, right[k]), old(right[k]) == at(before_right, right[k])) using {
            old(right[k]) == at(after_mark, right[k]);
            0 <= k; k < n;
            separate(memory(right[0..n]), memory(visited[0..n]));
        };
        assumption();
    }

    have unmarked(at(before_right, visited), 0, n)
        <= old(unmarked(visited, 0, n)) by { simp(); }
    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0
    } by { assumption(); }
    let right_result = step(dfs(left, right, visited, n, right[cur], to), {});
    have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
        intro();
        extract(visited[to] == at(before_right, visited[to]));
        extract(at(before_right, visited[to]) == old(visited[to]));
        simp();
    }
    have visited[cur] != 0 by {
        instantiate(forall (k: int32) {
            0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
        }, cur) using { 0 <= cur; cur < n; at(before_right, visited[cur]) != 0; }
        assumption();
    }

    have forall (k: int32) {
        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
    } by { assumption(); }
    apply(marked_transitive(old(visited), at(before_right, visited), visited, n));

    have unmarked(visited, 0, n)
        <= unmarked(at(before_right, visited), 0, n) by { simp(); }
    have unmarked(visited, 0, n) <= old(unmarked(visited, 0, n)) by {
        arithmetic() using {
            unmarked(visited, 0, n)
                <= unmarked(at(before_right, visited), 0, n);
            unmarked(at(before_right, visited), 0, n)
                <= old(unmarked(visited, 0, n));
        }
    }
    if right_result != 0 {
        have exists (path: Path) {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), path) == to
        } by { simp(); }
        let (right_rest: Path) satisfy {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), right_rest) == to
        };
        have walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)) == to by {
            unfold(walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)));
            assumption();
        }
        apply(walk_frame(old(left), old(right), at(before_right, left), at(before_right, right), n, cur, Path::Right(right_rest)));
        have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
            witness(path = Path::Right(right_rest));
            simp() using {
                walk(old(left), old(right), cur, Path::Right(right_rest)) == walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest));
                walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)) == to;
            }
        }
        have 0 <= to and to < n and at(before_right, visited[to]) == 0 by {
            extract(0 <= to and to < n and at(before_right, visited[to]) == 0);
            assumption();
        }
        have old(visited[to]) == 0 by {
            if old(visited[to]) != 0 {
                instantiate(forall (k: int32) {
                    0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0
                }, to) using { 0 <= to; to < n; old(visited[to]) != 0; }
                contradiction(at(before_right, visited[to]) == 0);
            } else { simp(); }
        }

        step();
        simp();
    } else {

        have forall (k: int32) {
            0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                visited[at(before_right, left[k])] != 0 and visited[at(before_right, right[k])] != 0
        } by {
            extract(forall (k: int32) {
                0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                    visited[at(before_right, left[k])] != 0 and visited[at(before_right, right[k])] != 0
            });
            assumption();
        }
        have right_result == 0 implies visited[at(before_right, right[cur])] != 0 by {
            assumption();
        }
        have visited[at(before_right, right[cur])] != 0 by {
            extract(visited[at(before_right, right[cur])] != 0);
            assumption();
        }
        have forall (k: int32) {
            0 <= k and k < n and old(visited[k]) == 0 and visited[k] != 0 implies
                visited[old(left[k])] != 0 and visited[old(right[k])] != 0
        } by {
            intro(); intro();
            extract(0 <= k); extract(k < n);
            extract(old(visited[k]) == 0); extract(visited[k] != 0);
            instantiate(forall (k: int32) {
                0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n
            }, k) using { 0 <= k; k < n; }
            instantiate(forall (k: int32) {
                0 <= k and k < n implies old(left[k]) == at(after_mark, left[k])
            }, k) using { 0 <= k; k < n; }
            instantiate(forall (k: int32) {
                0 <= k and k < n implies old(left[k]) == at(before_right, left[k])
            }, k) using { 0 <= k; k < n; }
            instantiate(forall (k: int32) {
                0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n
            }, k) using { 0 <= k; k < n; }
            instantiate(forall (k: int32) {
                0 <= k and k < n implies old(right[k]) == at(after_mark, right[k])
            }, k) using { 0 <= k; k < n; }
            instantiate(forall (k: int32) {
                0 <= k and k < n implies old(right[k]) == at(before_right, right[k])
            }, k) using { 0 <= k; k < n; }
            if k == cur {
                have at(before_right, visited[old(left[k])]) != 0 by {
                    rewrite(old(left[k]) == at(after_mark, left[k]));
                    rewrite(k == cur);
                    assumption();
                }
                instantiate(forall (k: int32) {
                    0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
                }, old(left[k])) using {
                    0 <= old(left[k]); old(left[k]) < n;
                    at(before_right, visited[old(left[k])]) != 0;
                }
                have visited[old(right[k])] != 0 by {
                    rewrite(old(right[k]) == at(before_right, right[k]));
                    rewrite(k == cur);
                    assumption();
                }
                split();
            } else {
                if at(before_right, visited[k]) == 0 {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                            visited[at(before_right, left[k])] != 0 and visited[at(before_right, right[k])] != 0
                    }, k) using {
                        0 <= k; k < n; at(before_right, visited[k]) == 0; visited[k] != 0;
                    }
                    have visited[old(left[k])] != 0 by {
                        rewrite(old(left[k]) == at(before_right, left[k]));
                        simp();
                    }
                    have visited[old(right[k])] != 0 by {
                        rewrite(old(right[k]) == at(before_right, right[k]));
                        simp();
                    }
                    split();
                } else {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and k != cur implies old(visited[k]) == at(after_mark, visited[k])
                    }, k) using { 0 <= k; k < n; k != cur; }
                    have at(after_mark, visited[k]) == 0 by {
                        rewrite(at(after_mark, visited[k]) == old(visited[k])); assumption();
                    }
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
                            at(before_right, visited[at(after_mark, left[k])]) != 0 and at(before_right, visited[at(after_mark, right[k])]) != 0
                    }, k) using {
                        0 <= k; k < n; at(after_mark, visited[k]) == 0; at(before_right, visited[k]) != 0;
                    }
                    have at(before_right, visited[old(left[k])]) != 0 by {
                        rewrite(old(left[k]) == at(after_mark, left[k]));
                        simp();
                    }
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
                    }, old(left[k])) using {
                        0 <= old(left[k]); old(left[k]) < n;
                        at(before_right, visited[old(left[k])]) != 0;
                    }
                    have at(before_right, visited[old(right[k])]) != 0 by {
                        rewrite(old(right[k]) == at(after_mark, right[k]));
                        simp();
                    }
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
                    }, old(right[k])) using {
                        0 <= old(right[k]); old(right[k]) < n;
                        at(before_right, visited[old(right[k])]) != 0;
                    }
                    split();
                }
            }
        }
        have (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to } by {
            intro();
            apply(exhausted_zero_entry(old(left), old(right), old(visited), visited, n, cur, to)) using {
            0 <= cur; cur < n; visited[cur] != 0;
            forall (k: int32) { 0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n };
            forall (k: int32) { 0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n };
            forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 };
            forall (k: int32) {
            0 <= k and k < n and old(visited[k]) == 0 and visited[k] != 0 implies
                visited[old(left[k])] != 0 and visited[old(right[k])] != 0
        };
                0 <= to and to < n implies visited[to] == old(visited[to]);
            }
            assumption();
        }
        step();
        have result == 0 implies (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to } by { intro(); assumption(); }
        simp();
    }
}
```

```expect
pass
```
