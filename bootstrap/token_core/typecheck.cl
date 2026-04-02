(lambda
  infer
  (lambda
    alpha_eq
    (lambda
      whnf
      (lambda
        term
        (lambda
          expected_type
          (lambda
            ctx
            (app
              (lambda
                infer_result
                (if
                  (atom (var infer_result))
                  (cons
                    'err
                    (cons 'bad-infer-result nil))
                  (if
                    (atom_eq
                      (car (var infer_result))
                      'ok)
                    (if
                      (app
                        (app
                          (var alpha_eq)
                          (app
                            (var whnf)
                            (car (cdr (var infer_result)))))
                        (app
                          (var whnf)
                          (var expected_type)))
                      (cons
                        'ok
                        (cons (var expected_type) nil))
                      (cons
                        'err
                        (cons 'type-mismatch nil)))
                    (if
                      (atom_eq
                        (car (var infer_result))
                        'err)
                      (var infer_result)
                      (cons
                        'err
                        (cons 'bad-infer-result nil))))))
              (app
                (app
                  (var infer)
                  (var term))
                (var ctx)))))))))
