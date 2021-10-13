func main()
{
	const Int blength;
	const Int[] b;
	const Int n;
	Int[] a;

	Int i = 0;

	while(i < blength)
	{
		a[i] = b[i] + n;
		i = i + 1;
	}

}

(axiom
  (<= 1 blength)
)


(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 k)
				(< k blength)
			)
			(= (a main_end k) (+ (b k) n))
		)
	)
)
