func main()
{
	Int[] a;
	const Int[] b;

	const Int blength;

	Int i = 0;
	while(i < blength)
	{
		if(b[i] >= 0)
		{
			a[i] = b[i];
		}
		else
		{
			a[i] = 0-b[i];
		}
		i = i + 1;
	}
}

(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 k)
				(< k (value_const_int blength))
			)
			(or
				(= 
				    (select (value_arr main_end a) k) 
				    (select (value_const_arr b) k) 
				)
				(= 
				    (select (value_arr main_end a) k)
			        (- 0 (select (value_const_arr b) k)) 
				)
			)
		)
	)
)

(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 k)
				(< k (value_const_int blength))
			)
			(<= 0 (select (value_arr main_end a) k))
		)
	)
)
