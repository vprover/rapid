#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// generate a new array b containing all indices where the arrays a1 and a2 have the same value.
// Properties:
// 1) Each element of b corresponds to a position in a1/a2.
// 2) For each element of b, the elements in a1 and a2 at the corresponding index are the same.
// 3) If the elements in a1 and a2 are the same at position pos, then there exists an element in b with value pos.
// 4) If the elements in a1 and a2 are the same at position pos, then there exists an element in b with value pos, and that element is between 0 and blength.

func main()
{
	Const Int alength = nondet_int();
	Const Int* a1 = (Const Int*)malloc(sizeof(Const Int) * alength);
	Const Int* a2 = (Const Int*)malloc(sizeof(Const Int) * alength);
  
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		Int commonValue = nondet_int();
		a1[__i] = commonValue;
		a2[__i] = commonValue;
	}
	
	Int* b = (Const Int*)malloc(sizeof(Const Int) * alength);
	Int blength = 0;

	Int i = 0;
	while(i < alength) {
		if (a1[i] == a2[i]) {
			b[blength] = i;
			blength = blength + 1;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos); 
	assume(pos < blength);
	
	Bool exists = false;
	for (Int pos2 = 0; pos2 < alength; pos2++) {
		exists = exists || (b[pos2] == pos);
	}
	assert(exists);
}
