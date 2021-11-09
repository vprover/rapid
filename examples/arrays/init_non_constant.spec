// Variation of standard init example, where the value we initialize with depends on the iterator-value.
// Properties:
// 1) after the execution, a[pos] has the value 2*pos+v for each position pos in the array
// 2) if v is greater than 0, a[pos] is greater than 2*pos
// 3) if v is strictly greater than 0, a[pos] is strictly greater than 2*pos (variation of property 2)
// 4) if v is some positive constant, a[pos] is strictly greater than 2*pos (variation of property 2)

func main()
{
	Int[] a;
	const Int alength;
	const Int v;

	Int i = 0;
	while(i < alength)
	{
		a[i] = (2 * i) + v;
		i = i + 1;
	}
}

(axiom
  (<= 0 alength)
)

(conjecture
  (forall ((pos Int))
    (=>
       (and
          (<= 0 alength)
          (<= 0 pos)
          (< pos alength)
       )
       (= (a main_end pos) (+ (* 2 pos) v))
    )
  )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
            (<= 0 v)
         )
         (<= (* 2 pos) (a main_end pos))
      )
   )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
            (< 0 v)
         )
         (< (* 2 pos) (a main_end pos))
      )
   )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
            (= v 80)
         )
         (< (* 2 pos) (a main_end pos))
      )
   )
)