func main()
{
	const Int[] b;
	const Int blength;
	Int[] a;

	Int i = 0;

	while(i < blength)
	{
		a[i] = b[i];
		i = i + 1;
	}
}

(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 (value_const blength))
				(<= 0 j)
				(< j (value_const blength))
			)
			(= 
			    (select (value_arr main_end a) j) 
			    (select (value_const_arr b) j)
			)
		)
	)
)
