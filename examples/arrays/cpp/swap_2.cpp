#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int length = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * length);
	Int* b = (Int*)malloc(sizeof(Int) * length);
	assume(0 <= length);
	for (Int __i = 0; __i < length; __i++) {
		a[__i] = nondet_int();
		b[__i] = nondet_int();
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < length);
	Int al8 = a[pos];
	
	Int i = 0;
	while(i < length) {
		Int current = a[i];
		a[i] = b[i];
		b[i] = current;
		i = i + 1;
	}
	
	assert(b[pos] == al8);
}
