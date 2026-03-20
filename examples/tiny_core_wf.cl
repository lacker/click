#!/usr/bin/env click
((
  (lambda
    ((lambda
       ((car (cdr stack))
        (lambda
          (((car (cdr stack)) (car (cdr stack)))
           (car stack)))))
     (lambda
       ((car (cdr stack))
        (lambda
          (((car (cdr stack)) (car (cdr stack)))
           (car stack)))))))
  (lambda
    (lambda
      (if (atom (car stack))
          (if (atom_eq (car stack) nil)
              true
              (if (atom_eq (car stack) true)
                  true
                  (if (atom_eq (car stack) false)
                      true
                      (atom_eq (car stack) 'stack))))
          (if (atom (car (car stack)))
              (if (atom_eq (car (car stack)) 'quote)
                  (if (atom (cdr (car stack)))
                      false
                      (if (atom (cdr (cdr (car stack))))
                          (atom_eq (cdr (cdr (car stack))) nil)
                          false))
                  (if (atom_eq (car (car stack)) 'lambda)
                      (if (atom (cdr (car stack)))
                          false
                          (if (atom (cdr (cdr (car stack))))
                              (if (atom_eq (cdr (cdr (car stack))) nil)
                                  ((car (cdr stack)) (car (cdr (car stack))))
                                  false)
                              false))
                      (if (atom (cdr (car stack)))
                          false
                          (if (atom (cdr (cdr (car stack))))
                              (if (atom_eq (cdr (cdr (car stack))) nil)
                                  (if ((car (cdr stack)) (car (car stack)))
                                      ((car (cdr stack)) (car (cdr (car stack))))
                                      false)
                                  false)
                              false))))
              (if (atom (cdr (car stack)))
                  false
                  (if (atom (cdr (cdr (car stack))))
                      (if (atom_eq (cdr (cdr (car stack))) nil)
                          (if ((car (cdr stack)) (car (car stack)))
                              ((car (cdr stack)) (car (cdr (car stack))))
                              false)
                          false)
                      false)))))))
 (quote ((lambda stack) (quote a))))
