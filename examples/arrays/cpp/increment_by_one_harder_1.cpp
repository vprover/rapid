#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"
// harder version of increment_by_one (it is harder, since the array we read from is the same array we write to)
// increment each position in the array by one, then check that every position was incremented by 1
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_43_true-unreach-call_ground.c,
// 1) original property
// 2) slightly-rewritten property

func main()
{
	Const Int alength = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * alength);
	Int* al12 = (Int*)malloc(sizeof(Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		Int value = nondet_int();
		a[__i] = value;
		al12[__i] = value;
	}
	Int i = 0;

	while (i < alength) {
		a[i] = a[i] + 1;
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	assert(al12[pos] == a[pos] - 1);
}
