(lambda whnf
  (lambda structural_equal
    (lambda recur
      (lambda term
        (if
          (atom (var term))
          (var term)
          (app
            (lambda normalized_list
              (if
                (atom (car (var normalized_list)))
                (if
                  (atom_eq (car (var normalized_list)) 'app)
                  (if
                    (atom (cdr (var normalized_list)))
                    (var normalized_list)
                    (if
                      (atom (cdr (cdr (var normalized_list))))
                      (var normalized_list)
                      (if
                        (atom (cdr (cdr (cdr (var normalized_list)))))
                        (if
                          (atom_eq
                            (cdr (cdr (cdr (var normalized_list))))
                            nil)
                          (app
                            (lambda reduced
                              (if
                                (app
                                  (app (var structural_equal) (var reduced))
                                  (var normalized_list))
                                (var normalized_list)
                                (app (var recur) (var reduced))))
                            (app (var whnf) (var normalized_list)))
                          (var normalized_list))
                        (var normalized_list))))
                  (var normalized_list))
                (var normalized_list)))
            (cons
              (app (var recur) (car (var term)))
              (app (var recur) (cdr (var term))))))))))
