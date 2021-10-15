#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

// Harder versions of some of the properties from partition-example
// 1) each element in b is a copy of some element in a, which fulfils the range-bounds of a
// 2) each element in c is a copy of some element in a, which fulfils the range-bounds of a
// 3) for each element in a, which is greater or equal 0, there exists a copy of that element in b, which fulfils the range-bounds of b
// 4) for each element in a, which is smaller than 0, there exists a copy of that element in c, which fulfils the range-bounds of c
// 5) for each element in a, either there exists a copy of that element in b, which fulfils the range-bounds of b, or there exists a copy of that element in c, which fulfils the range-bounds of c

func main()
{
	Const Int alength = nondet_int();
	Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
	
	Int* b = (Int*)malloc(sizeof(Int) * alength);
	Int blength = 0;
	Int* c = (Int*)malloc(sizeof(Int) * alength);
	Int clength = 0;
	
	Int i = 0;
	while (i < alength) {
		assume(blength <= i);
		assume(clength <= i);
		if (a[i] >= 0) {
			b[blength] = a[i];
			blength = blength + 1;
		}
		else {
			c[clength] = a[i];
			clength = clength + 1;
		}
		i = i + 1;
	}
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	
	Bool exists1 = false;
	for (Int pos2 = 0; pos2 < blength; pos2++) {
		exists1 = exists1 || (b[pos2] == a[pos]);
	}
	Bool exists2 = false;
	for (Int pos2 = 0; pos2 < clength; pos2++) {
		exists2 = exists2 || (c[pos2] == a[pos]);
	}
	assert(exists1 || exists2);
}