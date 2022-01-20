// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_two_index_01.c

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
		(= (i (l8 it)) (j (l8 it)))
	)
)

(axiom
  (<= 0 blength)
)

(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 blength)
				(<= 0 k)
				(< k blength)
			)
			(= (a main_end k) (b k))
		)
	)
)
