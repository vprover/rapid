#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int blength = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * blength);
	assume(1 <= blength);
	for (Int __i = 0; __i < blength; __i++) {
		b[__i] = nondet_int();
	}
	Const Int n = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * blength);

	Int i = 0;

	while (i < blength) {
		a[i] = b[i] + n;
		i = i + 1;
	}

	Int k = nondet_int();
	assume(0 <= k);
	assume(k < blength);
	assert(a[k] == b[k] + n);
}
