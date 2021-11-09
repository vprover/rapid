#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// The find example from the Invgen-repo where we want to prove that
// 1) if we find a position, the element at that position is equal to v
// 2) variation of property 1)
// 3) variation of property 1)
// 4) variation of property 1)
// 5) forall positions pos between 0 and r, A[pos] is different from v

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	Const Int v = nondet_int();

	assume(0 <= alength);
	
	Int i = 0;
	Int r = alength;

	while (i < alength && r == alength) {
		if (a[i] == v) {
			r = i;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos && pos < r);
	assert(a[pos] != v);
}
