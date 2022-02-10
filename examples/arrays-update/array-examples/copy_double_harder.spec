// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_copy2_ground-2.c


func main(){
	const Int[] b;
	const Int length;
    Int[] c;
	Int[] a;

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
			(= (c main_end j) (b j))
		)
	)
)
