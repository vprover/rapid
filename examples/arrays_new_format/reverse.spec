// similar to copy, but in reverse

func main()
{
	Int[] a;
	const Int[] b;
	const Int length;

	Int i = 0;
	while(i < length)
	{
		a[i] = b[length - 1 - i];
		i = i + 1;
	}
}

(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 (value_const_int length))
				(<= 0 j)
				(< j (value_const_int length))
			)
			(= 
			    (select (value_arr main_end a) j) 
			    (select (value_const_arr b) (- (- (value_const_int length) 1) j)) 
			)
		)
	)
)
