func main()
{
	const Int alength;
	Int[] a;

	Int i = 0;
	const Int n;

	while(i < alength)
	{
		a[i] = a[i] + n;
		i = i + 1;
	}

	Int j = 0;

	while(j < alength)
	{
		a[j] = a[j] - n;
		j = j + 1;
	}

}

(axiom
  (<= 0 alength)
)


(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 k)
				(< k (+ alength 5))
			)
			(= (a main_end k) (a l6 k))
		)
	)
)
