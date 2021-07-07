// Variation of init_non_constant, where multiplication is removed.
// Properties:
// 1) after the execution, a[pos] has the value pos+v for each position pos in the array
// 2) if v is greater than 0, a[pos] is greater than pos
// 3) if v is strictly greater than 0, a[pos] is strictly greater than pos (variation of property 2)
// 4) if v is some positive constant, a[pos] is strictly greater than pos (variation of property 2)

func main()
{
	Int[] a;
	const Int alength;
	const Int v;

	Int i = 0;
	while(i < alength)
	{
		a[i] = i + v;
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
         (= (select (value_arr main_end a) pos) (+ pos (value_const_int v)))
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
         (<= pos (select (value_arr main_end a) pos))
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
         (< pos (select (value_arr main_end a) pos))
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
         (< pos (select (value_arr main_end a) pos))
      )
   )
)