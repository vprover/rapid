func main()
{
	const Int[] a;
	const Int alength;
	const Int x;

	Int i = 0;
	while(i < alength)
	{
		if (a[i] == x)
		{
			break;
		}
		else 
		{
			skip;
		}
		i = i + 1;
	}
}

(conjecture
	(=>
		(and
			(<= 0 x)
			(< x alength)
			(<= 0 alength)
		)
		(or
			(= x (a (i main_end)))
			(= (i main_end) alength)
		)
	)
)

(conjecture
	(=>
		(and
			(< (i main_end) alength)
			(<= 0 alength)
		)
		(= x (a (i main_end)))
	)
)

(conjecture
	(=>
		(and
			(< alength (i main_end))
			(<= 0 alength)
		)
		(forall ((pos Int))
			(=>
				(and
					(<= 0 pos)
					(< pos alength)
				)
				(not
					(= (a pos) x)
				)
			)
		)
	)
)