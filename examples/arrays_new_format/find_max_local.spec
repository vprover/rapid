func main()
{
	const Int[] a;
	const Int alength;

	Int[] b;
	
	b[0] = a[0];
	Int blength = 1;

	Int i = 1;
	Int m = 0;
	while (i < alength)
	{
		if (a[i] > a[m])
		{
			b[i] = a[i];
			blength = blength + 1;
			m = i;
		}
		else
		{
			skip;
		}
		i = i + 1;
	}
}

(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 1 (value_const_int alength))
				(<= 0 k)
				(< k (value_const_int alength))
				(forall ((l Int))
					(=>
						(and
							(<= 0 l)
							(< l k)
						)
						(< (select (value_const_arr a) l) (select (value_const_arr a) k))
					)
				)
			)
			(exists ((j Int))
				(and
					(<= 0 j)
					(< j (value_int main_end blength))
					(= (select (value_const_arr a) k) (select (value_arr main_end b) j))
				)
			)
		)
	)
)

(conjecture
	(forall ((j Int))
		(exists ((k Int))
			(=>
				(and
					(<= 1 (value_const_int alength))
					(<= 0 j)
					(< j (value_int main_end blength))
				)
				(and
					(<= 0 k)
					(< k (value_const_int alength))
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
				(<= 1 (value_const_int alength))
				(<= 0 j)
				(<= 0 k)
				(<= j k)
				(< k (value_int main_end blength))
			)
			(<= (select (value_arr main_end b) j) (select (value_arr main_end b) k))
		)
	)
)
