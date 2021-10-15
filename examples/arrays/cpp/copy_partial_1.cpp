#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Int alength = 0;
	Const Int blength = nondet_int();
	Const Int* b = (Const Int*)malloc(sizeof(Int) * blength);
	Int* a = (Int*)malloc(sizeof(Int) * blength);
	for (Int __i = 0; __i < blength; __i++) {
		b[__i] = nondet_int();
	}
	Const Int k = nondet_int();

	assume(k <= blength);
	assume(0 <= blength);
	
	while (alength < k) {
		a[alength] = b[alength];
		alength = alength + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < k);
	assert(a[j] == b[j]);
}
