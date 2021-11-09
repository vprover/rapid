// for each position, add the elements of array a and b and save the result in array c.
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_seq_init_true-unreach-call_ground.c,
// but subtraction replaced by addition

func main()
{
	const Int[] a;
	const Int[] b;
	Int[] c;
	const Int length;

	Int i = 0;
	while(i < length)
	{
		c[i] = a[i] + b[i];
		i = i + 1;
	}
}

(axiom
  (<= 0 length)
)

(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 j)
				(< j length)
				(<= 0 length)
			)
			(= (c main_end j) (+ (a j) (b j)) )
		)
	)
)
