(lambda recur
  (lambda req
    (if (atom (var req))
        false
        (if (atom (car (var req)))
            (if (atom_eq (car (var req)) 'contains)
                (if (atom (car (cdr (cdr (var req)))))
                    false
                    (if (atom_eq (car (car (cdr (cdr (var req)))))
                                 (car (cdr (var req))))
                        true
                        (app (var recur)
                             (cons 'contains
                                   (cons (car (cdr (var req)))
                                         (cons (cdr (car (cdr (cdr (var req)))))
                                               nil))))))
                (if (atom_eq (car (var req)) 'wf)
                    (if (atom (car (cdr (var req))))
                        (if (atom_eq (car (cdr (var req))) nil)
                            true
                            (if (atom_eq (car (cdr (var req))) true)
                                true
                                (atom_eq (car (cdr (var req))) false)))
                        (if (atom (car (car (cdr (var req)))))
                            (if (atom_eq (car (car (cdr (var req)))) 'quote)
                                (if (atom (cdr (car (cdr (var req)))))
                                    false
                                    (if (atom (cdr (cdr (car (cdr (var req))))))
                                        (if (atom_eq (cdr (cdr (car (cdr (var req))))) nil)
                                            true
                                            false)
                                        false))
                                (if (atom_eq (car (car (cdr (var req)))) 'var)
                                    (if (atom (cdr (car (cdr (var req)))))
                                        false
                                        (if (atom (cdr (cdr (car (cdr (var req))))))
                                            (if (atom_eq (cdr (cdr (car (cdr (var req))))) nil)
                                                (if (atom (car (cdr (car (cdr (var req))))))
                                                    (app (var recur)
                                                         (cons 'contains
                                                               (cons (car (cdr (car (cdr (var req)))))
                                                                     (cons (car (cdr (cdr (var req))))
                                                                           nil))))
                                                    false)
                                                false)
                                            false))
                                    (if (atom_eq (car (car (cdr (var req)))) 'app)
                                        (if (atom (cdr (car (cdr (var req)))))
                                            false
                                            (if (atom (cdr (cdr (car (cdr (var req))))))
                                                false
                                                (if (atom (cdr (cdr (cdr (car (cdr (var req)))))))
                                                    (if (atom_eq (cdr (cdr (cdr (car (cdr (var req)))))) nil)
                                                        (if (app (var recur)
                                                                 (cons 'wf
                                                                       (cons (car (cdr (car (cdr (var req)))))
                                                                             (cons (car (cdr (cdr (var req))))
                                                                                   nil))))
                                                            (app (var recur)
                                                                 (cons 'wf
                                                                       (cons (car (cdr (cdr (car (cdr (var req))))))
                                                                             (cons (car (cdr (cdr (var req))))
                                                                                   nil))))
                                                            false)
                                                        false)
                                                    false)))
                                        (if (atom_eq (car (car (cdr (var req)))) 'lambda)
                                            (if (atom (cdr (car (cdr (var req)))))
                                                false
                                                (if (atom (cdr (cdr (car (cdr (var req))))))
                                                    false
                                                    (if (atom (cdr (cdr (cdr (car (cdr (var req)))))))
                                                        (if (atom_eq (cdr (cdr (cdr (car (cdr (var req)))))) nil)
                                                            (if (atom (car (cdr (car (cdr (var req))))))
                                                                (if (app (var recur)
                                                                         (cons 'contains
                                                                               (cons (car (cdr (car (cdr (var req)))))
                                                                                     (cons (car (cdr (cdr (var req))))
                                                                                           nil))))
                                                                    false
                                                                    (app (var recur)
                                                                         (cons 'wf
                                                                               (cons (car (cdr (cdr (car (cdr (var req))))))
                                                                                     (cons (cons (car (cdr (car (cdr (var req)))))
                                                                                                 (car (cdr (cdr (var req)))))
                                                                                           nil)))))
                                                                false)
                                                            false)
                                                        false)))
                                            false))))
                            false))
                    false))
            false))))
