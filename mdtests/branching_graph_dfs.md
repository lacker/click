# A cyclic, two-successor graph search

The C is the original two-successor graph search, unchanged.
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
        instantiate(forall (k: int32) { 0 <= k and k < n and a[k] != 0 implies b[k] != 0 }, k);
        instantiate(forall (k: int32) { 0 <= k and k < n and b[k] != 0 implies c[k] != 0 }, k);
        close();
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
    have forall (k: int32) {
        0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n
    } by { close(); }
    have forall (k: int32) {
        0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n
    } by { close(); }

    branch {
        true => {
            have (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to } by {
                intro();
                instantiate(forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }, cur);
                apply(0 <= cur and cur < n implies old(visited[cur]) == 0);
                contradiction(visited[cur] != 0);
            }

            have forall (k: int32) {
                0 <= k and k < n and old(visited[k]) == 0 and visited[k] != 0 implies
                    visited[old(left[k])] != 0 and visited[old(right[k])] != 0
            } by {
                intro(); intro();
                have old(visited[k]) == 0; have visited[k] != 0;
                contradiction(visited[k] != 0);
            }

            step();
            close();
        }
        false => {}
    }
    branch {
        true => {
            have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
                witness(Path::Here);
                unfold(walk(old(left), old(right), cur, Path::Here));
                close();
            }
            step();
            close();
        }
        false => {}
    }
    mark before_mark;
    step();

    have forall (k: int32) {
        0 <= k and k < n and k != cur implies visited[k] == old(visited[k])
    } by {
        intro(); intro();
        have cur != k by { close() using { k != cur; }; }
        have separate(memory(visited[cur]), memory(visited[k])) by {
            apply(click::separation::separate_elements(visited, cur, k));
        }
        have separate(statement(2).footprint, memory(visited[k])) by {
            normalize() using { separate(memory(visited[cur]), memory(visited[k])); };
        }
        have at(statement(2).exit, visited[k]) == at(statement(2).entry, visited[k]) by {
            preserve(memory(visited[k]), statement(2));
        }
        close();
    }

    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies visited[k] != 0
    } by {
        intro();
        intro();
        if k == cur {
            rewrite(k, cur);
            close();
        } else {
            instantiate(forall (k: int32) {
                0 <= k and k < n and k != cur implies visited[k] == old(visited[k])
            }, k);
            rewrite(visited[k], old(visited[k]));
            close();
        }
    }

    have forall (k: int32) { 0 <= k and k < cur implies at(before_mark, visited[k]) == visited[k] } by {
        intro(); intro();
        have 0 <= k by { close(); }
        have k < n by { close(); }
        have k != cur by { close(); }
        instantiate(forall (k: int32) {
            0 <= k and k < n and k != cur implies visited[k] == old(visited[k])
        }, k);
        close();
    }
    have forall (k: int32) { cur < k and k < n implies at(before_mark, visited[k]) == visited[k] } by {
        intro(); intro();
        have 0 <= k by { close(); }
        have k < n by { close(); }
        have k != cur by { close(); }
        instantiate(forall (k: int32) {
            0 <= k and k < n and k != cur implies visited[k] == old(visited[k])
        }, k);
        close();
    }
    have viewable(visited[0..n]) by { observe(visited[0..n]); }
    apply(unmarked_point_update(at(before_mark, visited), visited, 0, n, n, cur));
    apply(unmarked_nonnegative(visited, 0, n, n));
    have unmarked(visited, 0, n) < unmarked(at(before_mark, visited), 0, n) by {
        close() using {
            to_integer(unmarked(visited, 0, n)) == to_integer(unmarked(at(before_mark, visited), 0, n) - 1);
        };
    }
    observe(bounded_successors(left, right, n));
    have 0 <= left[cur] and left[cur] < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= left[k] and left[k] < n
        }, cur);
        close();
    }
    mark after_mark;

    have forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after_mark, left[k]) } by {
        intro(); intro();
        have separate(memory(visited[0..n]), memory(left[0..n])) by {
            apply(click::separation::separate_symm(memory(left[0..n]), memory(visited[0..n])));
        }
        have contains(memory(visited[0..n]), memory(visited[cur])) by {
            apply(click::separation::contains_element(visited, 0, n, cur));
        }
        have contains(memory(left[0..n]), memory(left[k])) by {
            apply(click::separation::contains_element(left, 0, n, k));
        }
        have separate(memory(visited[cur]), memory(left[k])) by {
            apply(click::separation::separate_restrict(memory(visited[0..n]), memory(left[0..n]), memory(visited[cur]), memory(left[k])));
        }
        have separate(statement(2).footprint, memory(left[k])) by {
            normalize() using { separate(memory(visited[cur]), memory(left[k])); };
        }
        have at(statement(2).exit, left[k]) == at(statement(2).entry, left[k]) by {
            preserve(memory(left[k]), statement(2));
        }
        close();
    }
    have forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(after_mark, right[k]) } by {
        intro(); intro();
        have separate(memory(visited[0..n]), memory(right[0..n])) by {
            apply(click::separation::separate_symm(memory(right[0..n]), memory(visited[0..n])));
        }
        have contains(memory(visited[0..n]), memory(visited[cur])) by {
            apply(click::separation::contains_element(visited, 0, n, cur));
        }
        have contains(memory(right[0..n]), memory(right[k])) by {
            apply(click::separation::contains_element(right, 0, n, k));
        }
        have separate(memory(visited[cur]), memory(right[k])) by {
            apply(click::separation::separate_restrict(memory(visited[0..n]), memory(right[0..n]), memory(visited[cur]), memory(right[k])));
        }
        have separate(statement(2).footprint, memory(right[k])) by {
            normalize() using { separate(memory(visited[cur]), memory(right[k])); };
        }
        have at(statement(2).exit, right[k]) == at(statement(2).entry, right[k]) by {
            preserve(memory(right[k]), statement(2));
        }
        close();
    }

    have 0 <= old(left[cur]) and old(left[cur]) < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n
        }, cur);
        close();
    }
    have 0 <= to and to < n implies at(after_mark, visited[to]) == old(visited[to]) by {
        intro();
        have to != cur by { close() using { cur != to; }; }
        instantiate(forall (k: int32) {
            0 <= k and k < n and k != cur implies visited[k] == old(visited[k])
        }, to);
        close();
    }
    let { result: left_result } = step(dfs);
    have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
        intro();
        have visited[to] == at(after_mark, visited[to]);
        have at(after_mark, visited[to]) == old(visited[to]);
        close();
    }
    have visited[cur] != 0 by {
        instantiate(forall (k: int32) {
            0 <= k and k < n and at(after_mark, visited[k]) != 0 implies visited[k] != 0
        }, cur);
        have 0 <= cur and cur < n and at(after_mark, visited[cur]) != 0 by { close(); }
        apply(0 <= cur and cur < n and at(after_mark, visited[cur]) != 0 implies visited[cur] != 0);
    }

    have forall (k: int32) {
        0 <= k and k < n and at(after_mark, visited[k]) != 0 implies visited[k] != 0
    } by { close(); }
    apply(marked_transitive(old(visited), at(after_mark, visited), visited, n));

    have unmarked(visited, 0, n) <= old(unmarked(visited, 0, n)) by {
        close() using {
            unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n);
            to_integer(unmarked(at(after_mark, visited), 0, n))
                == to_integer(unmarked(at(before_mark, visited), 0, n) - 1);
            unmarked(at(before_mark, visited), 0, n)
                == old(unmarked(visited, 0, n));
        };
    }
    branch {
        true => {
            have exists (path: Path) {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), path) == to
            } by {
                apply(left_result != 0 implies exists (path: Path) {
                    walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), path) == to
                });
            }
            let rest = obtain(exists (rest: Path) {
                walk(at(after_mark, left), at(after_mark, right), at(after_mark, left[cur]), rest) == to
            });
            have walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)) == to by {
                unfold(walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)));
                close();
            }
            apply(walk_frame(old(left), old(right), at(after_mark, left), at(after_mark, right), n, cur, Path::Left(rest)));
            have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
                witness(Path::Left(rest));
                close() using {
                    walk(old(left), old(right), cur, Path::Left(rest)) == walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest));
                    walk(at(after_mark, left), at(after_mark, right), cur, Path::Left(rest)) == to;
                };
            }
            have 0 <= to and to < n and at(after_mark, visited[to]) == 0;
            step();
            close();
        }
        false => {}
    }
    observe(bounded_successors(left, right, n));
    have viewable(visited[0..n]) by { observe(visited[0..n]); }
    apply(unmarked_nonnegative(visited, 0, n, n));
    have unmarked(visited, 0, n) < old(unmarked(visited, 0, n)) by {
        close() using {
            unmarked(visited, 0, n) <= unmarked(at(after_mark, visited), 0, n);
            to_integer(unmarked(at(after_mark, visited), 0, n))
                == to_integer(unmarked(at(before_mark, visited), 0, n) - 1);
            unmarked(at(before_mark, visited), 0, n)
                == old(unmarked(visited, 0, n));
        };
    }
    have 0 <= right[cur] and right[cur] < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= right[k] and right[k] < n
        }, cur);
        close();
    }
    mark before_right;
    have forall (k: int32) {
        0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
            at(before_right, visited[at(after_mark, left[k])]) != 0 and at(before_right, visited[at(after_mark, right[k])]) != 0
    } by {
        apply(left_result == 0 implies forall (k: int32) {
        0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
            at(before_right, visited[at(after_mark, left[k])]) != 0 and at(before_right, visited[at(after_mark, right[k])]) != 0
    });
    }
    have at(after_mark, left[cur]) == old(left[cur]) by {
        instantiate(forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after_mark, left[k]) }, cur);
        close();
    }
    have at(before_right, visited[at(after_mark, left[cur])]) != 0 by {
        apply(left_result == 0 implies at(before_right, visited[at(after_mark, left[cur])]) != 0);
    }

    have forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(before_right, left[k]) } by {
        intro(); intro();
        instantiate(forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after_mark, left[k]) }, k);
        have separate(memory(visited[0..n]), memory(left[0..n])) by {
            apply(click::separation::separate_symm(memory(left[0..n]), memory(visited[0..n])));
        }
        have contains(memory(visited[0..n]), statement(3).call(0).footprint) by { close(); }
        have contains(memory(left[0..n]), memory(left[k])) by {
            apply(click::separation::contains_element(left, 0, n, k));
        }
        have separate(statement(3).call(0).footprint, memory(left[k])) by {
            apply(click::separation::separate_restrict(memory(visited[0..n]), memory(left[0..n]), statement(3).call(0).footprint, memory(left[k])));
        }
        have at(statement(3).call(0).exit, left[k]) == at(statement(3).call(0).entry, left[k]) by {
            preserve(memory(left[k]), statement(3).call(0));
        }
        close();
    }
    have forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(before_right, right[k]) } by {
        intro(); intro();
        instantiate(forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(after_mark, right[k]) }, k);
        have separate(memory(visited[0..n]), memory(right[0..n])) by {
            apply(click::separation::separate_symm(memory(right[0..n]), memory(visited[0..n])));
        }
        have contains(memory(visited[0..n]), statement(3).call(0).footprint) by { close(); }
        have contains(memory(right[0..n]), memory(right[k])) by {
            apply(click::separation::contains_element(right, 0, n, k));
        }
        have separate(statement(3).call(0).footprint, memory(right[k])) by {
            apply(click::separation::separate_restrict(memory(visited[0..n]), memory(right[0..n]), statement(3).call(0).footprint, memory(right[k])));
        }
        have at(statement(3).call(0).exit, right[k]) == at(statement(3).call(0).entry, right[k]) by {
            preserve(memory(right[k]), statement(3).call(0));
        }
        close();
    }

    have forall (k: int32) {
        0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0
    } by { close(); }
    have 0 <= old(right[cur]) and old(right[cur]) < n by {
        instantiate(forall (k: int32) {
            0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n
        }, cur);
        close();
    }
    let { result: right_result } = step(dfs);
    have 0 <= to and to < n implies visited[to] == old(visited[to]) by {
        intro();
        have visited[to] == at(before_right, visited[to]);
        have at(before_right, visited[to]) == old(visited[to]);
        close();
    }
    have visited[cur] != 0 by {
        instantiate(forall (k: int32) {
            0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
        }, cur);
        have 0 <= cur and cur < n and at(before_right, visited[cur]) != 0 by { close(); }
        apply(0 <= cur and cur < n and at(before_right, visited[cur]) != 0 implies visited[cur] != 0);
    }

    have forall (k: int32) {
        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
    } by { close(); }
    apply(marked_transitive(old(visited), at(before_right, visited), visited, n));

    have unmarked(visited, 0, n) <= old(unmarked(visited, 0, n)) by {
        close() using {
            unmarked(visited, 0, n)
                <= unmarked(at(before_right, visited), 0, n);
            unmarked(at(before_right, visited), 0, n)
                <= old(unmarked(visited, 0, n));
        };
    }
    if right_result != 0 {
        have exists (path: Path) {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), path) == to
        } by {
            apply(right_result != 0 implies exists (path: Path) {
                walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), path) == to
            });
        }
        let right_rest = obtain(exists (right_rest: Path) {
            walk(at(before_right, left), at(before_right, right), at(before_right, right[cur]), right_rest) == to
        });
        have walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)) == to by {
            unfold(walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)));
            close();
        }
        apply(walk_frame(old(left), old(right), at(before_right, left), at(before_right, right), n, cur, Path::Right(right_rest)));
        have exists (path: Path) { walk(old(left), old(right), cur, path) == to } by {
            witness(Path::Right(right_rest));
            close() using {
                walk(old(left), old(right), cur, Path::Right(right_rest)) == walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest));
                walk(at(before_right, left), at(before_right, right), cur, Path::Right(right_rest)) == to;
            };
        }
        have 0 <= to and to < n and at(before_right, visited[to]) == 0;
        have old(visited[to]) == 0 by {
            if old(visited[to]) != 0 {
                instantiate(forall (k: int32) {
                    0 <= k and k < n and old(visited[k]) != 0 implies at(before_right, visited[k]) != 0
                }, to);
                apply(0 <= to and to < n and old(visited[to]) != 0 implies at(before_right, visited[to]) != 0);
                contradiction(at(before_right, visited[to]) == 0);
            } else { close(); }
        }

        step();
        close();
    } else {
        have forall (k: int32) {
            0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                visited[at(before_right, left[k])] != 0 and visited[at(before_right, right[k])] != 0
        } by {
            apply(right_result == 0 implies forall (k: int32) {
            0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                visited[at(before_right, left[k])] != 0 and visited[at(before_right, right[k])] != 0
        });
        }
        have visited[at(before_right, right[cur])] != 0 by {
            apply(right_result == 0 implies visited[at(before_right, right[cur])] != 0);
        }
        have forall (k: int32) {
                0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                    visited[old(left[k])] != 0 and visited[old(right[k])] != 0
            } by {
            intro(); intro();
            instantiate(forall (k: int32) {
                0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                    visited[at(before_right, left[k])] != 0 and visited[at(before_right, right[k])] != 0
            }, k);
            instantiate(forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(before_right, left[k]) }, k);
            rewrite(old(left[k]), at(before_right, left[k]));
            instantiate(forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(before_right, right[k]) }, k);
            rewrite(old(right[k]), at(before_right, right[k]));
            close();
        }
        have forall (k: int32) {
                0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
                    at(before_right, visited[old(left[k])]) != 0 and at(before_right, visited[old(right[k])]) != 0
            } by {
            intro(); intro();
            instantiate(forall (k: int32) {
                0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
                    at(before_right, visited[at(after_mark, left[k])]) != 0 and at(before_right, visited[at(after_mark, right[k])]) != 0
            }, k);
            instantiate(forall (k: int32) { 0 <= k and k < n implies old(left[k]) == at(after_mark, left[k]) }, k);
            rewrite(old(left[k]), at(after_mark, left[k]));
            instantiate(forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(after_mark, right[k]) }, k);
            rewrite(old(right[k]), at(after_mark, right[k]));
            close();
        }
        have forall (k: int32) {
            0 <= k and k < n and old(visited[k]) == 0 and visited[k] != 0 implies
                visited[old(left[k])] != 0 and visited[old(right[k])] != 0
        } by {
            intro(); intro();
            have 0 <= k; have k < n;
            have old(visited[k]) == 0; have visited[k] != 0;
            instantiate(forall (k: int32) {
                0 <= k and k < n implies 0 <= old(left[k]) and old(left[k]) < n
            }, k);
            instantiate(forall (k: int32) {
                0 <= k and k < n implies 0 <= old(right[k]) and old(right[k]) < n
            }, k);
            if k == cur {
                have at(before_right, visited[old(left[k])]) != 0 by {
                    rewrite(k, cur);
                    close();
                }
                instantiate(forall (k: int32) {
                    0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
                }, old(left[k]));
                have visited[old(right[k])] != 0 by {
                    rewrite(k, cur);
                    instantiate(forall (k: int32) { 0 <= k and k < n implies old(right[k]) == at(before_right, right[k]) }, cur);
                    rewrite(old(right[cur]), at(before_right, right[cur]));
                    close();
                }
                close();
            } else {
                if at(before_right, visited[k]) == 0 {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(before_right, visited[k]) == 0 and visited[k] != 0 implies
                            visited[old(left[k])] != 0 and visited[old(right[k])] != 0
                    }, k);
                    close();
                } else {
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
                            at(before_right, visited[old(left[k])]) != 0 and at(before_right, visited[old(right[k])]) != 0
                    }, k);
                    apply(0 <= k and k < n and at(after_mark, visited[k]) == 0 and at(before_right, visited[k]) != 0 implies
                        at(before_right, visited[old(left[k])]) != 0 and at(before_right, visited[old(right[k])]) != 0);
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
                    }, old(left[k]));
                    apply(0 <= old(left[k]) and old(left[k]) < n and at(before_right, visited[old(left[k])]) != 0 implies
                        visited[old(left[k])] != 0);
                    instantiate(forall (k: int32) {
                        0 <= k and k < n and at(before_right, visited[k]) != 0 implies visited[k] != 0
                    }, old(right[k]));
                    apply(0 <= old(right[k]) and old(right[k]) < n and at(before_right, visited[old(right[k])]) != 0 implies
                        visited[old(right[k])] != 0);
                    close();
                }
            }
        }
        have (forall (k: int32) { 0 <= k and k < n implies old(visited[k]) == 0 }) implies forall (path: Path) { walk(old(left), old(right), cur, path) != to } by {
            intro();
            apply(exhausted_zero_entry(old(left), old(right), old(visited), visited, n, cur, to));
            close();
        }
        step();
        close();
    }
}
```

```expect
pass
```
