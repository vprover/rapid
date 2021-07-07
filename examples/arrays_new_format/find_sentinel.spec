// start with an array which contains v at index j. Go through array until v is found at index i.
// Prove that i <= j (j and i don't need to be equal since there could be multiple v in the array).
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_sentinel_true-unreach-call_true-termination.c

func main()
{
	Int[] a;
	const Int j;
	const Int v;
	const Int alength;

	Int i = 0;
	a[j] = v;
	while (i < alength && a[i] != v)
	{
		i = i + 1;
	}
}

(conjecture
	(=>
		(and
			(<= 0 (value_const_int alength))
			(<= 0 (value_const_int j))
			(< (value_const_int j) (value_const_int alength))
		)
		(<= (value_int main_end i) (value_const_int j))
	)
)
