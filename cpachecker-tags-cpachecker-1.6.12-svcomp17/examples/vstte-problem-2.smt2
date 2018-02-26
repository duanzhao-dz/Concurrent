(set-logic AUFLIA)

(declare-fun a (Int) Int)
(declare-fun b (Int) Int)
(declare-fun alength () Int)
(declare-fun blength () Int)

(declare-fun sk_x () Int)
(declare-fun sk_y () Int)

(assert (= alength blength))
(assert (forall ((x Int)) (=> (<= 0 x)
                          (=> (< x blength)
                              (= (b (a x)) x)))))
(assert (forall ((q Int)) (=> (<= 0 q)
                          (=> (< q alength)
                              (exists ((w Int))
                                      (and (<= 0 w)
                                           (< w alength)
                                           (= (a w) q)))))))

; (assert (not (forall ((x Int) (y Int))
;                      (=> (<= 0 x)
;                      (=> (< x y)
;                      (=> (< y blength) 
;                          (not (= (b x) (b y)))))))))

(assert (not 
                     (=> (<= 0 sk_x)
                     (=> (< sk_x sk_y)
                     (=> (< sk_y blength) 
                         (not (= (b sk_x) (b sk_y))))))))

(check-sat)
(exit)