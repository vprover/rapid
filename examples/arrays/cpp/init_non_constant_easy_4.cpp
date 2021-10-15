#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// Variation of init_non_constant, where multiplication is removed.
// Properties:
// 1) after the execution, a[pos] has the value pos+v for each position pos in the array
// 2) if v is greater than 0, a[pos] is greater than pos
// 3) if v is strictly greater than 0, a[pos] is strictly greater than pos (variation of property 2)
// 4) if v is some positive constant, a[pos] is strictly greater than pos (variation of property 2)

func main()
{
	Const Int alength = nondet_int();
	Int* a = (Int*)malloc(sizeof(Int) * alength);
	Const Int v = nondet_int();
	assume(0 <= alength);

	Int i = 0;
	while (i < alength) {
		a[i] = i + v;
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	assume(v == 80);
	assert(pos < a[pos]);
}