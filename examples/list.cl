#!/usr/bin/env click
(app (lambda x (cons (var x) (cons 'b nil))) 'a)
