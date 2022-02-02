// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_copy4_ground-1.c
// Note there are copy examples like this with up to 9 consecutive loops. 

func main()
{
	const Int[] b;
	const Int length;
	Int[] a;
    Int[] c;
    Int[] d;
    Int[] e;

	Int i = 0;

	while(i < length){
		a[i] = b[i];
		i = i + 1;
	}
    i = 0;
    while(i < length){
		c[i] = a[i];
		i = i + 1;
	}
    i = 0;
    while(i < length){
		d[i] = c[i];
		i = i + 1;
	}
	i = 0;
    while(i < length){
		e[i] = d[i];
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
				(<= 0 length)
				(<= 0 j)
				(< j length)
			)
			(= (e main_end j) (b j))
		)
	)
)
