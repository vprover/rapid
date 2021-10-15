#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	
	assume(0 <= alength);
	
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}

	Int k = nondet_int();
	assume(0 <= k);
	assume(k < alength);
	
	Int al6 = a[k];
	
	Int i = 0;
	Const Int n = nondet_int();

	while(i < alength) {
		a[i] = a[i] + n;
		i = i + 1;
	}

	Int j = 0;

	while(j < alength) {
		a[j] = a[j] - n;
		j = j + 1;
	}
	
	assert(a[k] == al6);
}
