#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// initialize each position in the array to the value of the previous position + 1, starting with value v for the first element
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_seq_init_true-unreach-call_ground.c

func main()
{
	Const Int alength = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * alength);
	Const Int v = nondet_int();
	assume(0 <= alength);

	Int i = 0;
	a[0] = v;
	while ((i + 1) < alength) {
		a[i + 1] = a[i] + 1;
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos && 0 <= pos + 1); // avoid overflows
	assume(pos + 1 < alength);
	assert(a[pos] < a[pos + 1]);
}