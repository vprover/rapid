#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// increment each position in the array by one, then check that every position was incremented by 1
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_43_true-unreach-call_ground.c,
// 1) original property
// 2) slightly-rewritten property

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	Int* b = (Int*)malloc(sizeof(Int) * alength);

	Int i = 0;

	while (i < alength) {
		b[i] = a[i] + 1;
		i = i + 1;
	}
	Int pos = nondet_int();
	assume(0 <= pos && pos < alength);
	assert(b[pos] == a[pos] + 1);
}
