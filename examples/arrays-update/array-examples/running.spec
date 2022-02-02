// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_running-1.c
// note we use symbolic values instead of integer constants

func main()
{
	const Int[] a;
	Int[] b;
	const Int length;
    Int f = 1;
    const Int k;
    const Int l;

	Int i = 0;
	while(i < length)
	{
        if (a[i] >= 0) {
            b[i] = k;
        } else {
            b[i] = l;
        }
		i = i + 1;

        if (a[i] >= 0 && b[i] != k) {
            f = 0;
        }else {
            skip;
        }
        if (a[i] < 0 && b[i] != l) {
            f = 0;
        }else {
            skip;
        }
	}
}

(axiom
  (<= 0 length)
)

(conjecture 
    (=>
        (<= 0 length)
        (= (f main_end) 1)
	)
)
