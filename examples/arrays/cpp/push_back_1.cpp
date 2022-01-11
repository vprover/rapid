#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"
// similar to copy, but keeps track of the size of a and asserts the property with respect to the size of a

func main()
{
	Const Int blength = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * blength);
	assume(0 <= blength);
	for (Int __i = 0; __i < blength; __i++) {
		b[__i] = nondet_int();
	}
	Int* a = (Int*)malloc(sizeof(Int) * blength);
	
	Int alength = 0;
	Int i = 0;
	while (i < blength) {
		assume(alength <= i);
		a[i] = b[i];
		alength = alength + 1;
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < alength);
	assert(a[j] == b[j]);
}
