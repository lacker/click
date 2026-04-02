(lambda recur
  (lambda left
    (lambda right
      (if (atom (var left))
          (if (atom (var right))
              (atom_eq (var left) (var right))
              false)
          (if (atom (var right))
              false
              (if (app (app (var recur) (car (var left))) (car (var right)))
                  (app (app (var recur) (cdr (var left))) (cdr (var right)))
                  false))))))
