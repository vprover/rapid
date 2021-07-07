func main()
{
	Int[] a;
	const Int alength;

	Int i = 0;

	while (i < alength)
	{
		if(a[i] < 0)
		{
			a[i] = 0;
		}
		else
		{
			skip;
		}
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
			(<= 0 (select (value_arr main_end a) pos))
		)
	)
)
