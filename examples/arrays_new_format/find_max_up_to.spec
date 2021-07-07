
func main()
{
	const Int[] a;
	const Int alength;
	Int[] b;

	Int i = 0;
	Int m = 0;
	while (i < alength)
	{
		if (a[i] > a[m])
		{
			b[i] = a[i];
			m = i;
		}
		else
		{
			b[i] = a[m];
		}
		i = i + 1;
	}
}

(conjecture
	(forall ((j Int)(k Int))
		(=>
			(and
				(<= 0 (value_const_int alength))
				(<= 0 j)
				(<= 0 k)
				(<= j k)
				(< k (value_const_int alength))
			)
			(<= (select (value_const_arr a) j) (select (value_arr main_end b) k))
		)
	)
)

(conjecture
	(forall ((j Int))
		(exists ((k Int))
			(=>
				(and
					(<= 0 (value_const_int alength))
					(<= 0 j)
					(< j (value_const_int alength))
				)
				(and
					(<= 0 k)
					(<= k j)
					(= (select (value_arr main_end b) j) (select (value_const_arr a) k))
				)
			)
		)
	)
)

(conjecture
	(forall ((j Int)(k Int))
		(=>
			(and
				(<= 0 (value_const_int alength))
				(<= 0 j)
				(<= 0 k)
				(<= j k)
				(< k (value_const_int alength))
			)
			(<= (select (value_arr main_end b) j) (select (value_arr main_end b) k))
		)
	)
)
