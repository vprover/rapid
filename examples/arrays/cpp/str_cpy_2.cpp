#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

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
	while (i < length && b[i] != 0) {
		a[i] = b[i];
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < i);
	assert(a[pos] != 0);
}
