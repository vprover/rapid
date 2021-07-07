func main()
{
	Int[] a;
	Int[] b;

	const Int length;

	Int i = 0;
	while(i < length)
	{
		Int current = a[i];
		a[i] = b[i];
		b[i] = current;
		i = i + 1;
	}
}

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int length))
				(<= 0 pos)
				(< pos (value_const_int length))
			)
			(= (select (value_arr main_end a) pos) (select (value_arr l8 b) pos))
		)
	)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int length))
				(<= 0 pos)
				(< pos (value_const_int length))
			)
			(= (select (value_arr main_end b) pos) (select (value_arr l8 a) pos))
		)
	)
)