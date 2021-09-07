// increment each position in the array by one, then check that every position was incremented by 1
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_43_true-unreach-call_ground.c,
// 1) original property
// 2) slightly-rewritten property

func main()
{
	const Int[] a;
	Int[] b;
	const Int alength;

	Int i = 0;

	while (i < alength)
	{
		b[i] = a[i] + 1;
		i = i + 1;
	}
}

(axiom
  (<= 0 alength)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 alength)
				(<= 0 pos)
				(< pos alength)
			)
			(= (a pos) (- (b main_end pos) 1))
		)
	)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 alength)
				(<= 0 pos)
				(< pos alength)
			)
			(= (b main_end pos) (+ (a pos) 1))
		)
	)
)
