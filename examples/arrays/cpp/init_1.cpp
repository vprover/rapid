#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * alength);
	Const Int v = nondet_int();
	assume(0 <= alength);

	Int i = 0;
	while(i < alength) {
		a[i] = v;
		i = i + 1;
	}
	Int pos = nondet_int();
	assume(0 <= pos && pos < alength);
	assert(a[pos] == v);
}
