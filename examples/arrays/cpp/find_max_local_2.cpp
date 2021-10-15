#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	const Int alength = nondet_int();
	const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(1 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	Int* b = (Int*)malloc(sizeof(Int) * alength);
	
	b[0] = a[0];
	Int blength = 1;

	Int i = 1;
	Int m = 0;
	while (i < alength) {
		if (a[i] > a[m]) {
			b[blength] = a[i];
			blength = blength + 1;
			m = i;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(1 <= alength);
	assume(0 <= j && j < blength);
	
	Bool exists = false;
	for (Int k = 0; k < alength; k++) {
		exists = exists || (b[j] == a[k]);
	}
	assert(exists);
}
