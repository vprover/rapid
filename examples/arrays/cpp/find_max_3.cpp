#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		Int nondet = nondet_int();
		assume(0 > nondet);
		a[__i] = nondet;
	}
	

	Int i = 0;
	Int max = 0;
	while (i < alength) {
		if (a[i] > max) {
			max = a[i];
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	assert(max == 0);
}
