#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * alength);
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
	assume(pos < alength);
	assert(c[pos * 2 + 1] == b[pos]);
}
