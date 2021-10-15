#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(1 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	Int* b = (Int*)malloc(sizeof(Int) * alength);
	
	b[0] = a[0];
	Int blength = 1;

	Int i = 0;
	Int m = 0;
	while (i < alength) {
		if (a[i] < a[m]) {
			b[i] = a[i];
			blength = blength + 1;
			m = i;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int k = nondet_int();
	assume(0 <= k && k < alength);
	
	Bool all = true;
	for (Int l = 0; l < k; l++) {
		all = all && (a[k] < a[l]);
	}
	assume(all);
	
	Bool exists = false;
	for (Int j = 0; j < blength; j++) {
		exists = exists || (a[k] == b[j]);
	}
	
	assert(exists);
}
