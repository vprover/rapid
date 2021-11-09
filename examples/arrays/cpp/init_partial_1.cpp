#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * alength);
	Const Int k = nondet_int();
	assume(0 <= alength);
	assume(k <= alength);

	Int i = 0;
	while (i < k) {
		a[i] = 0;
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < k);
	assert(a[pos] == 0);
}
