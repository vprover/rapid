#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// check whether two arrays are the same at each position. If not, set the flag r to 1.
// Prove that if flag was not set to 1, then arrays are equal.
// similar to all of the following examples:
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_compare_true-unreach-call_ground.c
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_strcmp_true-unreach-call_ground.c
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_password_true-unreach-call_ground.c

#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// check whether two arrays are the same at each position. If not, set the flag r to 1.
// Prove that if flag was not set to 1, then arrays are equal.
// similar to all of the following examples:
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_compare_true-unreach-call_ground.c
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_strcmp_true-unreach-call_ground.c
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_password_true-unreach-call_ground.c

func main()
{
	Const Int length = nondet_int();
	Const Int* a  = (Const Int*)malloc(sizeof(Const Int) * length);
	Const Int* b  = (Const Int*)malloc(sizeof(Const Int) * length);
	assume(0 <= length);
  	for (Int __i = 0; __i < length; __i++) {
		a[__i] = nondet_int();
		b[__i] = nondet_int();
	}

	Int r = 0;
	Int i = 0;
	while (i < length) {
		if (a[i] != b[i]) {
			r = 1;
		}
		else {
			skip;
		}
		i = i + 1;
	}
	
	Int k = nondet_int();
	assume(0 <= k && k < length && r != 1);
	assert(a[k] == b[k]);
}
