
(set-logic AUFLIA)

(declare-fun a.select (Int Int) Int)
(declare-fun a.store (Int Int Int) Int)

(declare-fun a () Int)
(declare-fun b () Int)

(assert (forall ((?a Int) (?i Int) (?v Int)) (! (= (a.select (a.store ?a ?i ?v) ?i) ?v) :pattern ((a.store ?a ?i ?v)) )))
(assert (forall ((?a Int) (?i Int) (?v Int) (?j Int)) (! (or (= ?i ?j) (= (a.select (a.store ?a ?i ?v) ?j) (a.select ?a ?j))) :pattern ((a.select (a.store ?a ?i ?v) ?j)) )))

(assert (not (exists ((x Int) (y Int) (z Int)) (=> (= b (a.store a x 2)) (= (a.select b y) (a.select a z))))))
;(assert (not (=> (= b (a.store a 1 2)) (= (a.select b 2) (a.select a 2)))))

(check-sat)
