#!/usr/bin/env click
(app
  (lambda code
    (if (atom (var code))
        false
        (if (atom (car (var code)))
            (if (atom_eq (car (var code)) 'lambda)
                (car (cdr (var code)))
                false)
            false)))
  '(lambda x (var x)))
