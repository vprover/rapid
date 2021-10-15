#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
    Int i;
    Const Int alength = nondet_int();
    Const Int* a = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
    Const Int val2 = 3;
    Const Int val1 = 7;
    Const Int low=2;

    i = alength - 2; 

    while (i >= (0-1)) {
        if (i >= 0) {
            a[i] = val1;
        } 
		else {
            skip;
        }
        a[i + 1] = val2;
        i = i - 1; 
    }
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	assert(a[pos] >= low);
}
