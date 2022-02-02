// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_copy2_ground-1.c


func main()
{
	const Int[] b;
	const Int blength;
    const Int[] c;
	const Int clength;
	Int[] a;

	Int i = 0;

	while(i < blength)
	{
		a[i] = b[i];
		i = i + 1;
	}
    i = 0;
    while(i < clength)
	{
		a[i] = c[i];
		i = i + 1;
	}
}

(axiom
  (<= 0 blength)
)

(axiom
  (<= 0 clength)
)


(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 clength)
				(<= 0 j)
				(< j clength)
                (= blength clength)
			)
			(= (a main_end j) (c j))
		)
	)
)
