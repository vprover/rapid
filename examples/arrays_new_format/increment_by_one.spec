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

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int alength))
				(<= 0 pos)
				(< pos (value_const_int alength))
			)
			(= (select (value_const_arr a) pos) (- (select (value_arr main_end b) pos) 1))
		)
	)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int alength))
				(<= 0 pos)
				(< pos (value_const_int alength))
			)
			(= (select (value_arr main_end b) pos) (+ (select (value_const_arr a) pos) 1))
		)
	)
)
