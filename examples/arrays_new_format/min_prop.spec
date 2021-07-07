func main()
{
	Int[] a;
  const Int[] b;
	const Int blength;

	Int i = 0;
	while(i < blength)
	{
    if(b[i] < 0)
    {
       a[i] = b[i];
    }
    else
    {
       a[i] = 0;
    }
		i = i + 1;
	}
}

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (value_const_int blength))
            (<= 0 (value_const_int blength))
         )
         (<= (select (value_arr main_end a) pos) 0)
      )
   )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (value_const_int blength))
            (<= 0 (value_const_int blength))
         )
         (or
            (= (select (value_arr main_end a) pos) 0)
            (= (select (value_arr main_end a) pos) (select (value_const_arr b) pos))
         )
      )
   )
)
