#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// for each position p: if a[p] is 1, set b[p] to 1, otherwise set it to zero.
// Prove that either both a[p] is 1 and b[p] is 1, or both a[p] is not 1 and b[p] is zero
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_running_true-unreach-call.c
// but simplified

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	Int* b = (Int*)malloc(sizeof(Const Int) * alength);

	Int i = 0;
	while(i < alength) {
		if (a[i] == 1) {
			b[i] = 1;
		}
		else {
			b[i] = 0;
		}
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < alength);
	assert((a[j] == 1 && b[j] == 1) || (a[j] != 1 && b[j] == 0));
}
