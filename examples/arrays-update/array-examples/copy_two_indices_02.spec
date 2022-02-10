// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_two_index_03.c
// variation from with symbolic v https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_two_index_02.c

func main()
{
	Int[] a;
	const Int[] b;
	const Int blength;
	Int i = 0;
	Int j = 0;
    const Int v;
	while(i < blength)
	{
		a[i] = b[j];
		i = i + 1;
		j = j + v;
	}
}

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
                (< 0 v)
			)
			(= (a main_end k) (b (+ (* v k) 1)))
		)
	)
)
