#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int length = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * length);
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * length);
	for (Int __i = 0; __i < length; __i++) {
		a[__i] = nondet_int();
		b[__i] = nondet_int();
	}
	Int* c = (Int*)malloc(sizeof(Int) * length);
	assume(0 <= length);
	
	Int i = 0;
	Int clength = 0;
	while(i < length) {
		if (a[i] == b[i]) {
			c[clength] = i;
			clength = clength + 1;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos && pos < clength);
	assert(a[c[pos]] == b[c[pos]]);
}
