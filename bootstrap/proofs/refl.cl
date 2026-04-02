(lambda A type
  (lambda x (var A)
    (lambda P (pi z (var A) type)
      (lambda px (app (var P) (var x))
        (var px)))))
