#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int blength = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * blength);
	Int* a = (Int*)malloc(sizeof(Const Int) * blength);
	assume(0 <= blength);
	for (Int __i = 0; __i < blength; __i++) {
		b[__i] = nondet_int();
	}


	Int i = 0;
	while (i < blength) {
		if (b[i] >= 0) {
			a[i] = b[i];
		}
		else {
			a[i] = 0 - b[i];
		}
		i = i + 1;
	}
	
	Int k = nondet_int();
	assume(0 <= k);
	assume(k < blength);
	assert(a[k] == b[k] || a[k] == -b[k]);
}
