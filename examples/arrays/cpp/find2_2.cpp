#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// a new encoding of find, which is easier for the solvers, where we want to prove that
// 1) if we find a position, the element at that position is equal to v
// 2) variation of property 1)
// 3) variation of property 1)
// 4) variation of property 1)
// 5) forall positions pos between 0 and i, A[pos] is different from v

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(int) * alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	Const Int v = nondet_int();
	
	assume(0 <= alength);
	
	Int i = 0;
	while (i < alength && a[i] != v) {
		i = i + 1;
	}
	
	assume(i < alength);
	assert(a[i] == v);
}
