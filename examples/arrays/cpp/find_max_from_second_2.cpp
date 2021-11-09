#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// find the maximal element in the array
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_27_true-unreach-call_ground.c

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(1 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}

	Int i = 1;
	Int max = a[0];
	while (i < alength) {
		if (a[i] > max) {
			max = a[i];
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Bool exists = false;
	for (Int k = 0; k < alength; k++) {
		exists = exists || (a[k] == max);
	}
	assert(exists);
}
