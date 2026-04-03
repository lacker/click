(lambda A type
  (lambda x (var A)
    (lambda y (var A)
      (lambda eq_xy
        (pi P (pi z (var A) type)
          (pi px (app (var P) (var x))
            (app (var P) (var y))))
        (lambda P (pi z (var A) type)
          (lambda py (app (var P) (var y))
            (app
              (app
                (app
                  (app
                    (var eq_xy)
                    (lambda z (var A)
                      (pi Q (pi w (var A) type)
                        (pi qz (app (var Q) (var z))
                          (app (var Q) (var x))))))
                  (lambda Q (pi w (var A) type)
                    (lambda qx (app (var Q) (var x))
                      (var qx))))
                (var P))
              (var py))))))))
