; main()
; {
;    i = 0 @l7
;    while ((i < length) && (!(b[i] == 0))) @l8
;    {
;       a[i] = b[i] @l10
;       i = (i) + (1) @l11
;    }
; }
; 

(set-logic UFDTLIA)

(declare-sort Location 0)
(declare-nat Nat zero s p Sub)
(declare-sort Time 0)
(declare-sort Trace 0)

(declare-datatypes ( (Node 0) ) (
( (node (data Int) (next Location) )))
)

(declare-fun value_int (Time Location) Int)
(declare-fun value_arr (Time Location) (Array Int Int))
(declare-fun value_node (Time Location) Node)
(declare-fun value_const_int (Location) Int)
(declare-fun value_const_arr (Location) (Array Int Int))
(declare-fun deref (Time Location) Location)
(declare-fun fin_list (Time Location) Bool)
(declare-fun length (Time Location) Nat)
(declare-fun item (Time Nat Location) Location)
(declare-const null Location)

(declare-const j Location)
(declare-const k Location)
(declare-const i Location)
(declare-const nl4 Nat)
(declare-fun l4 (Nat) Time)
(declare-fun l5 (Nat) Time)
(declare-fun l6 (Nat) Time)
(declare-fun l7 (Nat) Time)
(declare-fun l8 (Nat) Time)
(declare-const l2 Time)
(declare-const l10 Time)
(declare-const l11 Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-const tp Time)

(assert
   (and
      ;Update variable a at location l2
      (and
         (= (deref (l4 zero) j) null)
         (forall ((mem-loc Location))
            (=>
               (not
                  (= mem-loc j)
               )
               (= (deref (l4 zero) mem-loc) (deref l2 mem-loc))
            )
         )
      )

      ;Loop at location l4
      (and
         ;Jumping into the loop body doesn't change the variable values
         (forall ((Itl4 Nat))
            (=>
               (Sub Itl4 nl4)
               (and
                  (= (deref (l5 Itl4) j) (deref (l4 Itl4) j))
               )
            )
         )
         ;Semantics of the body
         (forall ((Itl4 Nat))
            (=>
               (Sub Itl4 nl4)
               (and
                  ;Update variable k at location l5
                  (and
                     (= (deref (l6 Itl4) k) 
                        (deref (l5 Itl4) 
                          (next (value_node  (l5 Itl4)  (deref (l5 Itl4)  i) ) ) )
                     )
                     (forall ((mem-loc Location))
                        (=>
                           (not
                              (= mem-loc k)
                           )
                           (= (deref (l6 Itl4) mem-loc) (deref (l5 Itl4) mem-loc))
                        )
                     )
                  )

                  ;Update next(I) at location l6
                  (and
                     (= (deref (l6 Itl4) j) 
                        (deref (l7 Itl4) 
                          (next (value_node  (l7 Itl4)  (deref (l7 Itl4)  i) ) ) )
                     )
                     (forall ((mem-loc Location))
                        (=>
                           (not
                              (= mem-loc (next (value_node  (l7 Itl4)  (deref (l7 Itl4)  i) ) ) )
                           )
                           (= (deref (l7 Itl4) mem-loc) (deref (l6 Itl4) mem-loc))
                        )
                     )
                  )

                  ;Update j at location l7
                  (and
                     (= (deref (l8 Itl4) j) 
                        (deref (l7 Itl4) i))
                     (forall ((mem-loc Location))
                        (=>
                           (not
                              (= mem-loc j )
                           )
                           (= (deref (l8 Itl4) mem-loc) (deref (l7 Itl4) mem-loc))
                        )
                     )
                  )

                  ;Update i at location l8
                  (and
                     (= (deref (l4 (s Itl4)) i) 
                        (deref (l8 Itl4) k))
                     (forall ((mem-loc Location))
                        (=>
                           (not
                              (= mem-loc i )
                           )
                           (= (deref (l4 (s Itl4)) mem-loc) (deref (l8 Itl4) mem-loc))
                        )
                     )
                  )

               )
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl4 Nat))
            (=>
               (Sub Itl4 nl4)
               (not (= (deref (l4 Itl4) i) null))
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (= (deref (l4 nl4) i) null)
         ;The values after the while-loop are the values from the last iteration
         (and
            (= (deref l10 i) (deref (l4 nl4) i))
            (= (deref l10 j) (deref (l4 nl4) j))
            (= (deref l10 k) (deref (l4 nl4) k))
            (forall ((n Node))
               (= (deref l10 (next n)) (deref (l4 nl4) (next n)))
            )                        
         )
      )

      ;Update i at l11
      (and
         (= (deref main_end i) (deref l11 j))
         (forall ((mem-loc Location))
            (=>
               (not
                  (= mem-loc i)
               )
               (= (deref main_end mem-loc) (deref l11 mem-loc))
            )
         )
      )         
      
   )
)

; Axiom: Semantics of memory locations
(assert
   (and
      (not
         (= j k)
      )
      (not
         (= j i)
      )
      (not
         (= i k)
      )
      (forall ((tp Time)(mem-loc Location))
         (not
            (= mem-loc (deref tp mem-loc))
         )
      )
      (forall ((n Nat) (tp Time))
         (and
            (not (= i (next (value_node tp (item tp n i) ) )))
            (not (= j (next (value_node tp (item tp n i) ) )))
            (not (= k (next (value_node tp (item tp n i) ) )))
         )
      )
      (forall ((n1 Node) (n2 Node))
         (=>
            (not (= n1 n2))
            (not 
               (= (next n1) (next n2))
            )
         )
      )      
   )
)


; item axiom 1
(assert
   (forall ((tp Time) (i Nat))
      (= 
         (item tp i null)
         null
      )
   )
)

; item axiom 2
(assert
   (forall ((tp Time) (x Location))
      (= 
         (item tp zero x)
         x
      )
   )
)

; item axiom 2
(assert
   (forall ((tp Time) (i Nat) (x Location))
      (= 
         (item tp (s i) x)
         (item tp i (next (value_node tp (deref tp x))))
      )
   )
)

; length axiom 1
(assert
   (forall ((tp Time))
      (= 
         (length tp null)
         zero
      )
   )
)

; length axiom 2
(assert
   (forall ((x Location)(tp Time))
      (=>
         (not (= x null))
         (= 
            (length tp x)
            (s (length tp (next (value_node tp (deref tp x)))))     
         )
      )
   )
)

; Fin_list axiom 1
(assert
   (forall ((tp Time))
      (fin_list tp null)
   )
)

; Fin_list axiom 1
(assert
   (forall ((x Location)(tp Time))
      (=>
         (not (= x null))   
         (= 
            (fin_list tp x)
            (fin_list tp (next (value_node tp (deref tp x))))     
         )
      )
   )
)

(assert-not
   (=>
      (fin_list l2 i)
      (= (item l2 zero i) (item main_end (length main_end i) i))
   )
)

(check-sat)

