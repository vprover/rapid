// harder version of increment_by_one (it is harder, since the array we read from is the same array we write to)
// increment each position in the array by one, then check that every position was incremented by 1
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_43_true-unreach-call_ground.c,
// 1) original property
// 2) slightly-rewritten property

func main()
{
	Int[] a;
	const Int alength;

	Int i = 0;

	while (i < alength)
	{
		a[i] = a[i] + 1;
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
			(= (select (value_arr l12 a) pos) (- (select (value_arr main_end a) pos) 1))
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
			(= (select (value_arr main_end a) pos) (+ (select (value_arr l12 a) pos) 1))
		)
	)
)
