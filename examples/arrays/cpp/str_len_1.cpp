#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int length = nondet_int(); // Had to be added to make this example translatable...
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * length);
	assume(0 <= length); // --||--
	for (Int __i = 0; __i < length; __i++) {
		a[__i] = nondet_int();
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < length); // --||--
	assume(a[pos] == 0);
	
	Int i = 0;
	while (a[i] != 0) {
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < i);
	assert(a[j] != 0);
}