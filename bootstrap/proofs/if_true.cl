(lambda A type
  (lambda t (var A)
    (lambda f (var A)
      (lambda P (pi z (var A) type)
        (lambda px (app (var P) (var t))
          (var px))))))
