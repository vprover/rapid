func main()
{
	const Int[] a;
	const Int alength;
	Int[] b;

	Int i = 0;
	Int m = 0;
	while (i < alength)
	{
		if (a[i] < a[m])
		{
			b[i] = a[i];
			m = i;
		}
		else
		{
			b[i] = a[m];
		}
		i = i + 1;
	}
}

(axiom
  (<= 0 alength)
)

(conjecture
	(forall ((j Int)(k Int))
		(=>
			(and
				(<= 0 alength)
				(<= 0 j)
				(<= 0 k)
				(<= j k)
				(< k alength)
			)
			(<= (b main_end k) (a j))
		)
	)
)

(conjecture
	(=>
		(<= 0 alength)
		(forall ((j Int))
			(exists ((k Int))
				(=>
					(and
						(<= 0 j)
						(< j alength)
					)
					(and
						(<= 0 k)
						(<= k j)
						(= (b main_end j) (a k))
					)
				)
			)
		)
	)
)

(conjecture
	(forall ((j Int)(k Int))
		(=>
			(and
				(<= 0 alength)
				(<= 0 j)
				(<= 0 k)
				(<= k j)
				(< j alength)
			)
			(<= (b main_end j) (b main_end k))
		)
	)
)
