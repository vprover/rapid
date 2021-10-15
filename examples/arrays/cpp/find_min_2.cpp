#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	
	Int k1 = nondet_int();
	assume (0 <= k1 && k1 < alength && a[k1] <= 0);

	Int i = 0;
	Int min = 0;
	while (i < alength) {
		if (a[i] < min) {
			min = a[i];
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Bool exists = false;
	for (Int k2 = 0; k2 < alength; k2++) {
		exists = exists || (a[k2] == min);
	}
	assert(exists);
}
