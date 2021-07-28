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

(declare-const a Location)
(declare-const b Location)
(declare-const c Location)
(declare-const j Location)
(declare-const k Location)
(declare-const i Location)

(declare-const l2 Time)
(declare-const l3 Time)
(declare-const l4 Time)
(declare-const l5 Time)
(declare-const l6 Time)

(declare-const l7 Time)
(declare-const l11 Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-const tp Time)

(assert
   (and
      (= (value_node l2 a) (node 2 null))
      ;Update variable a at location l2 

      (and
         (= (deref l3 k) a)
         (forall ((mem-loc Location))
            (= (value_node l3 mem-loc) (value_node l2 mem-loc) )
         )
      )

      (and
         (= (value_node l4 b) (node 2 k))
         (forall ((mem-loc Location))
            (and
               (= (deref l4 mem-loc) (deref l3 mem-loc) )
               (=>
                  (not
                     (= mem-loc b )
                  )
                  (= (value_node l4 mem-loc) (value_node l3 mem-loc))
               )
            )
         )
      )

      (and
         (= (deref l5 j) b)
         (forall ((mem-loc Location))
            (and
               (= (value_node l5 mem-loc) (value_node l4 mem-loc) )
               (=>
                  (not
                     (= mem-loc j )
                  )
                  (= (deref l5 mem-loc) (deref l4 mem-loc))
               )
            )
         )
      )

      (and
         (= (value_node l6 c) (node 2 j))
         (forall ((mem-loc Location))
            (and
               (= (deref l6 mem-loc) (deref l5 mem-loc) )
               (=>
                  (not
                     (= mem-loc c )
                  )
                  (= (value_node l6 mem-loc) (value_node l5 mem-loc))
               )
            )
         )
      )

      (and
         (= (deref main_end i) c)
         (forall ((mem-loc Location))
            (and
               (= (value_node main_end mem-loc) (value_node l6 mem-loc) )
               (=>
                  (not
                     (= mem-loc i )
                  )
                  (= (deref main_end mem-loc) (deref l6 mem-loc))
               )
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
      (not
         (= j a)
      )
      (not
         (= k a)
      )                
      (not
         (= j b)
      )
      (not
         (= k b)
      )
      (not
         (= j c)
      )
      (not
         (= k c)
      )                              
      (not
         (= a b)
      )
      (not
         (= a c)
      )      
      (not
         (= b c)
      )
      (not
         (= j null)
      )           
      (not
         (= k null)
      ) 
      (not
         (= i null)
      )                           
      (forall ((tp Time)(mem-loc Location))
         (not
            (= mem-loc (deref tp mem-loc))
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
      (=> 
         (not (= x null))
         (= 
            (item tp zero x)
            (deref tp x)
         )
      )
   )
)

; item axiom 2
(assert
   (forall ((tp Time) (i Nat) (x Location))
      (=> 
         (not (= x null))
         (= 
            (item tp (s i) x)
            (item tp i (next (value_node tp (deref tp x))))
         )
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
     (= (item main_end (s (s (s zero))) i) null)   
)

(check-sat)

