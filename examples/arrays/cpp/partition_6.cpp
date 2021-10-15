#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// Properties
// 1) each element in b is greater or equal 0
// 2) each element in c is smaller than 0
// 3) each element in b is a copy of some element in a
// 4) each element in c is a copy of some element in a
// 5) for each element in a, which is greater or equal 0, there exists a copy of that element in b
// 6) for each element in a, which is smaller than 0, there exists a copy of that element in c
// 7) for each element in a, there exists a copy of that element either in b or in c.

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}

	Int* b = (Int*)malloc(sizeof(Const Int) * alength);
	Int blength = 0;
	Int* c = (Int*)malloc(sizeof(Const Int) * alength);
	Int clength = 0;

	Int i = 0;
	while (i < alength) {
		if (a[i] >= 0) {
			b[blength] = a[i];
			blength = blength + 1;
		} 
		else {
			c[clength] = a[i];
			clength = clength + 1;
		}
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	assume(a[pos] < 0);
	
	Bool exists = false;
	for (Int pos2 = 0; pos2 < clength; pos2++) {
		exists = exists || (c[pos2] == a[pos]);
	}
	assert(exists);
}
