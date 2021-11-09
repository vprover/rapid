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
    Const Int low = 2;

    i = alength - 1; 

    while (i >= 0) {
        if((i - 1) >= 0) {
            a[i - 1] = i - 2;
        }
        else {
            skip;
        }
        a[i] = i;
        i = i - 1; 
    }
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	assert(a[pos] <= pos);
}
