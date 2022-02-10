// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_palindrome_ground.c

func main()
{
	const Int alength;
	Int[] a;

	Int i = 0;

	while(i < (alength / 2))
	{
		a[i] = a[alength-i-1];
		i = i + 1;
	}
}

(axiom
  (<= 0 alength)
)


(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 alength)
				(<= 0 j)
				(< j (div alength 2))
			)
			(= (a main_end j) (a main_end (- alength (- j 1))))
		)
	)
)
