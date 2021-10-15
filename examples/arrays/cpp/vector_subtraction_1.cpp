#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// for each position, subtract the element of array b from the element of array a and save the result in array c.
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_seq_init_true-unreach-call_ground.c,
// but subtraction replaced by addition

func main()
{
	Const Int length = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * length);
	Const Int* b = (Const Int*)malloc(sizeof(Const Int) * length);
	assume(0 <= length);
	for (Int __i = 0; __i < length; __i++) {
		a[__i] = nondet_int();
		b[__i] = nondet_int();
	}
	Int* c = (Int*)malloc(sizeof(Int) * length);

	Int i = 0;
	while(i < length) {
		c[i] = a[i] - b[i];
		i = i + 1;
	}
	
	Int j = nondet_int();
	assume(0 <= j);
	assume(j < length);
	assert(c[j] == a[j] - b[j]);
}
