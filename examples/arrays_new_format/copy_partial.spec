func main()
{
	Int[] a;
	Int alength = 0;
	const Int[] b;
	const Int blength;
	const Int k;

	while(alength < k)
	{
		a[alength] = b[alength];
		alength = alength + 1;
	}
}

(conjecture
	(=>
		(<= (value_const_int k) (value_const_int blength))
		(forall ((j Int))
			(=>
				(and
					(<= 0 j)
					(< j (value_const_int k))
				)
				(= 
				    (select (value_arr main_end a) j) 
				    (select (value_const_arr b) j)
				)
			)
		)
	)
)
