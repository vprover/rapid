// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_vararg_ground.c
// slightly rewritten loop condition to indicate size of the array

func main()
{
	const Int[] a;
	const Int alength;

	Int i = 0;

	while (a[i] >= 0 && i < alength) {
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
				(< pos (i main_end))
			)
			(<= 0 (a pos))
		)
	)
)
