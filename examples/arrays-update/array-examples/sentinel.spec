// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_sentinel-1.c

func main()
{
	Int[] a;
	const Int length;
    const Int position;
    const Int v; 
	Int i = 0;
    
    if (position >= 0 && position < length){
        a[position] = v; 
        while(a[i] != v){
            i = i + 1;
	    }
    } else {
        skip;
    }
	
}

(axiom
  (<= 0 length)
)

(conjecture
		(=>
			(and
				(<= 0 length)
                (<= 0 position)
                (< position length)
			)
			(<= (i main_end) position )
		)
)
