(lambda A type
  (lambda x (var A)
    (lambda y (var A)
      (lambda eq_xy
        (pi P (pi z (var A) type)
          (pi px (app (var P) (var x))
            (app (var P) (var y))))
        (lambda P (pi z (var A) type)
          (lambda px (app (var P) (var x))
            (app
              (app (var eq_xy) (var P))
              (var px))))))))
