func main()
{
	const Int[] a;
	const Int alength;

	Int i = 0;
	Int min = 0;
	while (i < alength)
	{
		if (a[i] < min)
		{
			min = a[i];
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
				(<= 0 (value_const_int alength))
				(<= 0 k)
				(< k (value_const_int alength))
			)
			(<= (value_int main_end min) (select (value_const_arr a) k))
		)
	)
)

(conjecture
	(=>
		(and
			(<= 0 (value_const_int alength))
			(exists ((k Int))
				(and
					(<= 0 k)
					(< k (value_const_int alength))
					(<= (select (value_const_arr a) k) 0)
				)
			)
		)
		(exists ((k Int))
			(and
				(<= 0 k)
				(< k (value_const_int alength))
				(= (select (value_const_arr a) k) (value_int main_end min))
			)
		)
	)
)

(conjecture
	(=>
		(and 
			(<= 0 (value_const_int alength))
			(forall ((k Int))
				(=>
					(and
						(<= 0 k)
						(< k (value_const_int alength))
					)
					(not (<= (select (value_const_arr a) k) 0))
				)
			)
		)
		(= (value_int main_end min) 0)
	)
)
