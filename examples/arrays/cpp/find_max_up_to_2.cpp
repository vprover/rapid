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
	Int* b = (Int*)malloc(sizeof(Int) * alength);

	Int i = 0;
	Int m = 0;
	while (i < alength) {
		if (a[i] > a[m]) {
			b[i] = a[i];
			m = i;
		}
		else {
			b[i] = a[m];
		}
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j && j < alength);
	
	Bool exists = false;
	for (Int k = 0; k <= j; k++) {
		exists = exists || (a[j] == a[k]);
	}
	
	assert(exists);
}
