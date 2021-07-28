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
(declare-const n Location)
(declare-const j Location)
(declare-const k Location)
(declare-const i Location)
(declare-const aSize Location)

(declare-const l2 Time)
(declare-fun l3 (Nat) Time)
(declare-fun l4 (Nat) Time)
(declare-fun l5 (Nat) Time)
(declare-fun l6 (Nat) Time)
(declare-fun l7 (Nat) Time)
(declare-const nl3 Nat)
(declare-fun malloc_node (Time) Location)

(declare-const l11 Time)
(declare-const main_end Time)
(declare-const t1 Trace)
(declare-const tp Time)

; Axiom: Semantics of function main
(assert
   (and
      (= (value_node l2 a) (node 2 null))
      ;Update variable a at location l2 

      (and
         (= (deref (l3 zero) k) a)
         (forall ((mem-loc Location))
            (= (value_node (l3 zero) mem-loc) (value_node l2 mem-loc) )
         )
      )

      ;Loop at location l7
      (and
         ;Jumping into the loop body doesn't change the variable values
         (forall ((Itl3 Nat))
            (=>
               (Sub Itl3 nl3)
               (and
                  (= (value_node (l4 Itl3) a) (value_node (l3 Itl3) a))
                  (= (deref (l4 Itl3) c) (deref (l3 Itl3) c))
                  (= (value_int (l4 Itl3) n) (value_int (l3 Itl3) n))
               )
            )
         )
         ;Semantics of the body
         (forall ((Itl3 Nat))
            (=>
               (Sub Itl3 nl3)
               (and
                  ;j points to newly malloced memory
                  (= (deref (l5 Itl3) j) (malloc_node (l4 Itl3)))
                  (forall ((mem-loc Location))
                     (and
                        (= (value_int (l5 Itl3) mem-loc) (value_int (l4 Itl3) mem-loc))                  
                        (=>
                           (not
                              (= mem-loc j)
                           )
                           (= (deref (l5 Itl3) mem-loc) (deref (l4 Itl3) mem-loc))
                        )
                     )
                  )      
               
                  ;next (deref j) points to what k points to
                  (= (deref (l6 Itl3) (next (value_node (l6 Itl3) (deref (l6 Itl3) j)) )) (deref (l5 Itl3) k))
                  (forall ((mem-loc Location))
                     (and
                        (= (value_int (l6 Itl3) mem-loc) (value_int (l5 Itl3) mem-loc))
                        (=>
                           (not
                              (= mem-loc (next (value_node (l6 Itl3) (deref (l6 Itl3) j)) ))
                           )
                           (= (deref (l6 Itl3) mem-loc) (deref (l5 Itl3) mem-loc))
                        )
                     )
                  )

                  ;set j to k 
                  (= (deref (l7 Itl3) k) (deref (l6 Itl3) j))
                  (forall ((mem-loc Location))
                     (and
                        (= (value_int (l7 Itl3) mem-loc) (value_int (l7 Itl3) mem-loc))
                        (=>
                           (not
                              (= mem-loc k)
                           )
                           (= (deref (l7 Itl3) mem-loc) (deref (l6 Itl3) mem-loc))
                        )
                     )
                  )

                  ;set  i to i+ 1
                  (= (value_int (l3 (s Itl3)) i) (+ (value_int (l7 Itl3) i) 1))
                  (forall ((mem-loc Location))
                     (= (deref (l3 (s Itl3)) mem-loc) (deref (l7 Itl3) mem-loc))
                  )
               )
            )
         )
         ;The loop-condition holds always before the last iteration
         (forall ((Itl3 Nat))
            (=>
               (Sub Itl3 nl3)
               (< (value_int (l3 Itl3) i) (value_const_int aSize))
            )
         )
         ;The loop-condition doesn't hold in the last iteration
         (not
            (< (value_int (l3 nl3) i) (value_const_int aSize))
         )
         ;The values after the while-loop are the values from the last iteration
         (and
            (= (value_int main_end i) (value_int (l3 nl3) i))
            (= (deref main_end j) (deref (l3 nl3) j))
            (= (deref main_end k) (deref (l3 nl3) k))
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
      (forall ((tp1 Time)(tp2 Time))
         (=> 
            (not (= tp1 tp2))
            (not
               (= (malloc tp1) (malloc tp2))
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

