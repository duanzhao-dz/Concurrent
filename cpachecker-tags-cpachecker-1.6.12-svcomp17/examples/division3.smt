(benchmark division3

 :logic AUFLIA
 :extrapreds ((divides Int Int))

 :assumption (forall (?x Int) (divides ?x 0))
 :assumption (forall (?x Int) (?y Int) (implies (divides ?x ?y)
                                                (and (divides ?x (+ ?y ?x))
                                                     (divides ?x (- ?y ?x)))))

 :assumption (not (exists (?x Int) (and (> ?x 0)
                                        (divides ?x 8)
                                        (divides ?x 12))))

 :formula true)