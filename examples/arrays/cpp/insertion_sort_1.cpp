#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Int i;
	Int j = 1;
	Int pivot;
	
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(2 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}

	while(j < alength) {
		pivot = a[j];
		i = j - 1;
		while(i >= 0 && a[i] > pivot) {
			a[i + 1] = a[i];
			i = i -1;
		}
		a[i + 1] = pivot;
		j = j + 1;
	}
	
	Int k = nondet_int();
	assume(0 <= k);
	assume(k < alength - 1);
	assert(a[k] <= a[k + 1]);
}
