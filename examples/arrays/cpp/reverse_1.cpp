#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// similar to copy, but in reverse

func main()
{
	Const Int length = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * length);
	assume(0 <= length);
	for (Int __i = 0; __i < length; __i++) {
		b[__i] = nondet_int();
	}
	Int* a = (Int*)malloc(sizeof(Int) * length);

	Int i = 0;
	while(i < length) {
		a[i] = b[length - 1 - i];
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < length);
	assert(a[j] == b[(length - 1) - j]);
}
