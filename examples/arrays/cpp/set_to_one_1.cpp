#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// If there is at least one iteration and therefore there is a last iteration, then in that last iteration, j is set to 1.
// Therefore it's 1 at the end of the loop.
// Seems to be difficult since we need to use the iteration before the last one.
// Update: should be solved by at-least-one-iteration lemma

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(int) * alength);
	assume(0 < alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}

	Int i = 0;
	Int j = 0;
	while(i < alength) {
		i = i + 1;
		j = 1;
	}
	
	assert(j == 1);
}
