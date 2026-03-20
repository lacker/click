#!/usr/bin/env click
((lambda
   (if (atom (car stack))
       false
       (if (atom (car (car stack)))
           (if (atom_eq (car (car stack)) 'closure)
               (if (atom (cdr (car stack)))
                   false
                   (if (atom (cdr (cdr (car stack))))
                       false
                       (if (atom (cdr (cdr (cdr (car stack)))))
                           (atom_eq (cdr (cdr (cdr (car stack)))) nil)
                           false)))
               false)
           false)))
 (lambda stack))
