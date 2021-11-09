#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * 2 * alength);
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * 2 * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
		b[__i] = nondet_int();
	}
	Int* c = (Int*)malloc(sizeof(Int) * 2 * alength);

	Int i = 0;
	while (i < alength) {
		c[i * 2] = a[i];
		c[i * 2 + 1] = b[i];
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength * 2);
	
	Bool exists = false;
	for (Int j = 0; j < 2 * alength; j++){
		exists = exists || (c[pos] == a[j] || c[pos] == b[j]);
	}
	assert(exists);
}