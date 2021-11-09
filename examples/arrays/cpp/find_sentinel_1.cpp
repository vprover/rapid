#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// start with an array which contains v at index j. Go through array until v is found at index i.
// Prove that i <= j (j and i don't need to be equal since there could be multiple v in the array).
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_sentinel_true-unreach-call_true-termination.c

func main()
{
	Const Int j = nondet_int();
	Const Int v = nondet_int();
	Const Int alength = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * alength);
	assume(0 <= alength);
	assume(0 <= j);
	assume(j < alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}

	Int i = 0;
	a[j] = v;
	while (i < alength && a[i] != v) {
		i = i + 1;
	}
	assert(i <= j);
}
