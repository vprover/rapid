func main()
{
	Int[] a;
	const Int[] b;
	const Int blength;

	Int i = 0;
	Int j = 0;
	while(i < blength)
	{
		a[i] = b[j];
		i = i + 1;
		j = j + 1;
	}
}

(axiom
	(forall ((it Nat))
		(= 
		    (value_int (l9 it) i) 
		    (value_int (l9 it) j)
		)
	)
)

(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 (value_const_int blength))
				(<= 0 k)
				(< k (value_const_int blength))
			)
			(= 
			    (select (value_arr main_end a) k) 
			    (select (value_const_arr b) k)
			)
		)
	)
)
