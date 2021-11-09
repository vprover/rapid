#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int blength = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * blength);
	Int* a = (Int*)malloc(sizeof(Int) * blength);
	assume(0 <= blength);
	for (Int __i = 0; __i < blength; __i++) {
		b[__i] = nondet_int();
	}

	Int i = 0;
	Int alength = 0;
	while (i < blength) {
		if (b[i] >= 0) {
			a[alength] = b[i];
			alength = alength + 1;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int k = nondet_int();
	assume(0 <= k);
	assume(k < alength);
	
	Bool exists = false;
	for (Int l = 0; l < blength; l++) {
		exists = exists || (a[k] == b[l]);
	}
	assert(exists);
}
