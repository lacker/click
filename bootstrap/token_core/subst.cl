(lambda recur
  (lambda term
    (lambda name
      (lambda replacement
        (if (atom (var term))
            (var term)
            (if (atom (car (var term)))
                (if (atom_eq (car (var term)) 'var)
                    (if (atom (cdr (var term)))
                        (var term)
                        (if (atom (cdr (cdr (var term))))
                            (if (atom_eq (cdr (cdr (var term))) nil)
                                (if (atom (car (cdr (var term))))
                                    (if (atom_eq (car (cdr (var term))) (var name))
                                        (var replacement)
                                        (var term))
                                    (var term))
                                (var term))
                            (var term)))
                    (if (atom_eq (car (var term)) 'app)
                        (if (atom (cdr (var term)))
                            (var term)
                            (if (atom (cdr (cdr (var term))))
                                (var term)
                                (if (atom (cdr (cdr (cdr (var term)))))
                                    (if (atom_eq (cdr (cdr (cdr (var term)))) nil)
                                        (cons 'app
                                              (cons (app
                                                      (app
                                                        (app (var recur)
                                                             (car (cdr (var term))))
                                                        (var name))
                                                      (var replacement))
                                                    (cons (app
                                                            (app
                                                              (app (var recur)
                                                                   (car
                                                                     (cdr
                                                                       (cdr
                                                                         (var term)))))
                                                              (var name))
                                                            (var replacement))
                                                          nil)))
                                        (var term))
                                    (var term))))
                        (if (atom_eq (car (var term)) 'lambda)
                            (if (atom (cdr (var term)))
                                (var term)
                                (if (atom (cdr (cdr (var term))))
                                    (var term)
                                    (if (atom (cdr (cdr (cdr (var term)))))
                                        (var term)
                                        (if (atom
                                              (cdr
                                                (cdr
                                                  (cdr
                                                    (cdr (var term))))))
                                            (if (atom_eq
                                                  (cdr
                                                    (cdr
                                                      (cdr
                                                        (cdr (var term)))))
                                                  nil)
                                                (if (atom (car (cdr (var term))))
                                                    (cons
                                                      'lambda
                                                      (cons
                                                        (car (cdr (var term)))
                                                        (cons
                                                          (app
                                                            (app
                                                              (app
                                                                (var recur)
                                                                (car
                                                                  (cdr
                                                                    (cdr
                                                                      (var term)))))
                                                              (var name))
                                                            (var replacement))
                                                          (cons
                                                            (if (atom_eq
                                                                  (car
                                                                    (cdr
                                                                      (var term)))
                                                                  (var name))
                                                                (car
                                                                  (cdr
                                                                    (cdr
                                                                      (cdr
                                                                        (var term)))))
                                                                (app
                                                                  (app
                                                                    (app
                                                                      (var recur)
                                                                      (car
                                                                        (cdr
                                                                          (cdr
                                                                            (cdr
                                                                              (var term))))))
                                                                    (var name))
                                                                  (var replacement)))
                                                            nil))))
                                                    (var term))
                                                (var term))
                                            (var term)))))
                            (if (atom_eq (car (var term)) 'pi)
                                (if (atom (cdr (var term)))
                                    (var term)
                                    (if (atom (cdr (cdr (var term))))
                                        (var term)
                                        (if (atom (cdr (cdr (cdr (var term)))))
                                            (var term)
                                            (if (atom
                                                  (cdr
                                                    (cdr
                                                      (cdr
                                                        (cdr (var term))))))
                                                (if (atom_eq
                                                      (cdr
                                                        (cdr
                                                          (cdr
                                                            (cdr (var term)))))
                                                      nil)
                                                    (if (atom
                                                          (car
                                                            (cdr (var term))))
                                                        (cons
                                                          'pi
                                                          (cons
                                                            (car
                                                              (cdr (var term)))
                                                            (cons
                                                              (app
                                                                (app
                                                                  (app
                                                                    (var recur)
                                                                    (car
                                                                      (cdr
                                                                        (cdr
                                                                          (var term)))))
                                                                  (var name))
                                                                (var replacement))
                                                              (cons
                                                                (if (atom_eq
                                                                      (car
                                                                        (cdr
                                                                          (var term)))
                                                                      (var name))
                                                                    (car
                                                                      (cdr
                                                                        (cdr
                                                                          (cdr
                                                                            (var term)))))
                                                                    (app
                                                                      (app
                                                                        (app
                                                                          (var recur)
                                                                          (car
                                                                            (cdr
                                                                              (cdr
                                                                                (cdr
                                                                                  (var term))))))
                                                                        (var name))
                                                                      (var replacement)))
                                                                nil))))
                                                        (var term))
                                                    (var term))
                                                (var term)))))
                                (var term)))))
                (var term)))))))
