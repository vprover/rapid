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
	
	Int k = nondet_int();
	assume(0 <= k && k < alength);
	assert(min <= a[k]);
}
