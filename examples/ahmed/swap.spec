;Func main {
;  Int * x, y;
;  Int a = *x;
;  Int b = *y;
;  *x = b;
;  *y = a;
;}


(set-logic UFDTLIA)

(declare-sort Time 0)
(declare-sort Trace 0)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const x Int)
(declare-const y Int)
(declare-const l0 Time) ;l0 is basically start_main
(declare-const l1 Time)
(declare-const l2 Time)
(declare-const l3 Time)
(declare-const l4 Time)
(declare-const junk Int)
(declare-fun deref (Int Time) Int)
(declare-fun val (Int Time) Int)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-const tp Time)

; Axiom: Semantics of function main
(assert
   (and
      ;assign arbitrary values to x and y 
      (= (val (deref x l0) l0) c)
      (= (val (deref y l0) l0) d)  
      ; x and y point to different locations
      (not (= (deref y l0) (deref x l0)))  

      (and
         (= a (val (deref x l0) l0))
         (forall ((loc Int))
            (and
               (= (deref loc l1) (deref loc l0))
               (= (val loc l1) (val loc l0))
            )
         )
      )
   
      (and
         (= b (val (deref y l1) l1))
         (forall ((loc Int))
            (and
               (= (deref loc l2) (deref loc l1))
               (= (val loc l2) (val loc l1))
            )
         )
      )

      (and
         (= (val (deref x l3) l3) b)
         (forall ((loc Int))
            (= (deref loc l3) (deref loc l2))
         )
         (forall ((loc Int))
            (=>
               (not (= loc (deref x l3)))
               (= (val loc l3) (val loc l2))
            )
         )
      )
      
      (and
         (= (val (deref y l4) l4) a)
         (forall ((loc Int))
            (= (deref loc l4) (deref loc l3))
         )
         (forall ((loc Int))
            (=>
               (not (= loc (deref y l4)))
               (= (val loc l4) (val loc l3))
            )
         )
      )
   )
)

; Conjecture: user-conjecture-0
(assert-not
   (and
      (=
        (val (deref y main_end) main_end)
        (val (deref x l0) l0)
      )
      (=
        (val (deref x main_end) main_end)
        (val (deref y l0) l0)      
      )      
   )
)

(check-sat)

