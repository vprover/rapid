
func main()
{
	const Int[] a;
	const Int alength;

	Int i = 0;
	Int max = 0;
	while (i < alength)
	{
		if (a[i] > max)
		{
			max = a[i];
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
			(<= (select (value_const_arr a) k) (value_int main_end max))
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
					(<= 0 (select (value_const_arr a) k))
				)
			)
		)
		(exists ((k Int))
			(and
				(<= 0 k)
				(< k (value_const_int alength))
				(= (select (value_const_arr a) k) (value_int main_end max))
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
					(not (<= 0 (select (value_const_arr a) k)))
				)
			)
		)
		(= (value_int main_end max) 0)
	)
)
