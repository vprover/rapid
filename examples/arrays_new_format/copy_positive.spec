func main()
{
	Int[] a;
	const Int[] b;
	const Int blength;

	Int i = 0;
	Int alength = 0;
	while(i < blength)
	{
		if (b[i] >= 0)
		{
			a[alength] = b[i];
			alength = alength + 1;
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
				(<= 0 k)
				(< k (value_int main_end alength))
				(<= 0 (value_const_int blength))
			)
			(<= 0 (select (value_arr main_end a) k))
		)
	)
)

(conjecture
	(forall ((k Int))
		(exists ((l Int))
			(=>
				(and
					(<= 0 k)
					(< k (value_int main_end alength))
					(<= 0 (value_const_int blength))
				)
				(= 
				    (select (value_arr main_end a) k) 
				    (select (value_const_arr b) l)
				)
			)
		)
	)
)
