func main()
{
	Int[] a;
	const Int alength;
	const Int k;

	Int i = 0;
	while (i < k)
	{
		a[i] = 0;
		i = i + 1;
	}
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (value_const_int k))
            (<= (value_const_int k) (value_const_int alength))
            (<= 0 (value_const_int alength))
         )
         (= (select (value_arr main_end a) pos) 0)
      )
   )
)
