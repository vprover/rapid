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

(conjecture
  (forall ((pos Int))
    (=>
       (and
          (<= 0 (value_const_int alength))
          (<= 0 pos)
          (< pos (value_const_int alength))
       )
       (= (select (value_arr main_end a) pos) (+ (* 2 pos) (value_const_int v)))
    )
  )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 (value_const_int alength))
            (<= 0 pos)
            (< pos (value_const_int alength))
            (<= 0 (value_const_int v))
         )
         (<= (* 2 pos) (select (value_arr main_end a) pos))
      )
   )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 (value_const_int alength))
            (<= 0 pos)
            (< pos (value_const_int alength))
            (< 0 (value_const_int v))
         )
         (< (* 2 pos) (select (value_arr main_end a) pos))
      )
   )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 (value_const_int alength))
            (<= 0 pos)
            (< pos (value_const_int alength))
            (= (value_const_int v) 80)
         )
         (< (* 2 pos) (select (value_arr main_end a) pos))
      )
   )
)