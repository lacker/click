(lambda recur
  (lambda name
    (lambda env
      (if (atom (var env))
          'missing
          (if (atom_eq (car (car (var env))) (var name))
              (cons 'found
                    (cons (car (cdr (car (var env))))
                          nil))
              (app
                (app (var recur) (var name))
                (cdr (var env))))))))
