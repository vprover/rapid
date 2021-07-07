func main()
{
	Int[] a;
	const Int alength;
	const Int v;

	Int i = 0;
	while(i < alength)
	{
		a[i] = v;
		i = i + 1;
	}
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (value_const_int alength))
            (<= 0 (value_const_int alength))
         )
         (= (select (value_arr main_end a) pos) (value_const_int v))
      )
   )
)
