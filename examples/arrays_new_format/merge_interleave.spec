func main()
{
	const Int[] a;
  const Int[] b;
  Int[] c;
	const Int alength;

	Int i = 0;
	while(i < alength)
	{
    c[i * 2] = a[i];
    c[i * 2 + 1] = b[i];
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
        (= (select (value_arr main_end c) (* pos 2)) (select (value_const_arr a) pos))
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
        )
        (= (select (value_arr main_end c) (+ (* pos 2) 1)) (select (value_const_arr b) pos))
      )
   )
)

(conjecture
   (forall ((pos Int))
      (exists ((j Int))
        (=>
          (and
            (<= 0 (value_const_int alength))
            (<= 0 pos)
            (< pos (value_const_int alength))
          )
          (or
            (= (select (value_arr main_end c) pos) (select (value_const_arr a) j))
            (= (select (value_arr main_end c) pos) (select (value_const_arr b) j))
          )
        )
      )
   )
)