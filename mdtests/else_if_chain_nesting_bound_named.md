# A long `else if` chain names the nesting bound

`pick` assigns from the first positive of thirteen arguments in one
`else if` chain. The proof writes one `branch` per test, each nested in the
previous `else` arm, so the regions nest thirteen deep, past the checked
drivers' bound of eleven.

The analyses that locate each region's end stop at that bound too, and past
it they used to give up before any driver reached its own depth check, so
the failure was reported as a shape "not implemented in this execution
context". The analyses now record the bound, and the failure names it.

```c filename=else_if_chain.c
int pick(int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int a8, int a9, int a10, int a11, int a12) {
    int s;
    s = 0;
    if (a0 > 0) {
        s = a0;
    } else if (a1 > 0) {
        s = a1;
    } else if (a2 > 0) {
        s = a2;
    } else if (a3 > 0) {
        s = a3;
    } else if (a4 > 0) {
        s = a4;
    } else if (a5 > 0) {
        s = a5;
    } else if (a6 > 0) {
        s = a6;
    } else if (a7 > 0) {
        s = a7;
    } else if (a8 > 0) {
        s = a8;
    } else if (a9 > 0) {
        s = a9;
    } else if (a10 > 0) {
        s = a10;
    } else if (a11 > 0) {
        s = a11;
    } else if (a12 > 0) {
        s = a12;
    }
    return 0;
}
```

```click
verifying "else_if_chain.c";

int pick(int a0, int a1, int a2, int a3, int a4, int a5, int a6, int a7, int a8, int a9, int a10, int a11, int a12) {
    ensures result == 0 by {
        step();
        step();
        branch {
            true => {
                step();
            }
            false => {
                branch {
                    true => {
                        step();
                    }
                    false => {
                        branch {
                            true => {
                                step();
                            }
                            false => {
                                branch {
                                    true => {
                                        step();
                                    }
                                    false => {
                                        branch {
                                            true => {
                                                step();
                                            }
                                            false => {
                                                branch {
                                                    true => {
                                                        step();
                                                    }
                                                    false => {
                                                        branch {
                                                            true => {
                                                                step();
                                                            }
                                                            false => {
                                                                branch {
                                                                    true => {
                                                                        step();
                                                                    }
                                                                    false => {
                                                                        branch {
                                                                            true => {
                                                                                step();
                                                                            }
                                                                            false => {
                                                                                branch {
                                                                                    true => {
                                                                                        step();
                                                                                    }
                                                                                    false => {
                                                                                        branch {
                                                                                            true => {
                                                                                                step();
                                                                                            }
                                                                                            false => {
                                                                                                branch {
                                                                                                    true => {
                                                                                                        step();
                                                                                                    }
                                                                                                    false => {
                                                                                                        branch {
                                                                                                            true => {
                                                                                                                step();
                                                                                                            }
                                                                                                            false => {
                                                                                                            }
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        step();
        close();
    }
}
```

```expect
fail: checked execution-region recursion exceeds the supported depth of 11
```
