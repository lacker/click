(lambda A type
  (lambda x (var A)
    (lambda y (var A)
      (lambda z (var A)
        (lambda eq_xy
          (pi P (pi w (var A) type)
            (pi px (app (var P) (var x))
              (app (var P) (var y))))
          (lambda eq_yz
            (pi P (pi w (var A) type)
              (pi py (app (var P) (var y))
                (app (var P) (var z))))
            (lambda P (pi w (var A) type)
              (lambda px (app (var P) (var x))
                (app
                  (app (var eq_yz) (var P))
                  (app
                    (app (var eq_xy) (var P))
                    (var px)))))))))))
