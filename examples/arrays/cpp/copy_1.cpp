#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int blength = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(int) * blength);
	assume(0 <= blength);
	for (Int __i = 0; __i < blength; __i++) {
		b[__i] = nondet_int();
	}
	Int* a = (Int*)malloc(sizeof(Int) * blength);

	Int i = 0;

	while (i < blength) {
		a[i] = b[i];
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < blength);
	assert(a[j] == b[j]);
}
