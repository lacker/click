(lambda wf
  (lambda subst
    (lambda recur
      (lambda term
        (if (app
              (var wf)
              (cons 'wf
                    (cons (var term)
                          (cons nil nil))))
            (if (atom (var term))
                (if (atom_eq (var term) 'type)
                    (cons 'ok
                          (cons 'type nil))
                    (cons 'err
                          (cons 'unknown-atom nil)))
                (if (atom_eq (car (var term)) 'var)
                    (cons 'err
                          (cons 'unbound-variable nil))
                    (if (atom_eq (car (var term)) 'lambda)
                        (cons 'ok
                              (cons (var term) nil))
                        (if (atom_eq (car (var term)) 'pi)
                            (cons 'ok
                                  (cons (var term) nil))
                            (if (atom_eq (car (var term)) 'app)
                                (app
                                  (lambda fun_result
                                    (if (atom_eq (car (var fun_result)) 'ok)
                                        (app
                                          (lambda arg_result
                                            (if (atom_eq
                                                  (car (var arg_result))
                                                  'ok)
                                                (app
                                                  (lambda fun_value
                                                    (app
                                                      (lambda arg_value
                                                        (if (atom (var fun_value))
                                                            (cons
                                                              'err
                                                              (cons
                                                                'not-a-function
                                                                nil))
                                                            (if (atom_eq
                                                                  (car
                                                                    (var
                                                                      fun_value))
                                                                  'lambda)
                                                                (app
                                                                  (var recur)
                                                                  (app
                                                                    (app
                                                                      (app
                                                                        (var
                                                                          subst)
                                                                        (car
                                                                          (cdr
                                                                            (cdr
                                                                              (cdr
                                                                                (var
                                                                                  fun_value))))))
                                                                      (car
                                                                        (cdr
                                                                          (var
                                                                            fun_value))))
                                                                    (var
                                                                      arg_value)))
                                                                (cons
                                                                  'err
                                                                  (cons
                                                                    'not-a-function
                                                                    nil)))))
                                                      (car
                                                        (cdr
                                                          (var
                                                            arg_result)))))
                                                  (car
                                                    (cdr
                                                      (var fun_result))))
                                                (var arg_result)))
                                          (app
                                            (var recur)
                                            (car
                                              (cdr
                                                (cdr
                                                  (var term))))))
                                        (var fun_result)))
                                  (app
                                    (var recur)
                                    (car
                                      (cdr
                                        (var term)))))
                                (cons 'err
                                      (cons 'unknown-form nil)))))))
            (cons 'err
                  (cons 'malformed nil)))))))
