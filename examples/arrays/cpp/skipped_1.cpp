#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
    Const Int alength = nondet_int(); 
    Const Int* a  = (Const Int*)malloc(sizeof(Const Int) * alength);
	assume(0 <= alength);
	for (Int __i = 0; __i < alength; __i++) {
		a[__i] = nondet_int();
	}
    Int i = 1;

    while(i <= alength) {
        if (a[2 * i - 2] > 2 * i - 2){
            a[2 * i - 2] = 2 * i - 2;
        } else {
            skip;
        }
        if (a[2 * i - 1] > 2 * i - 1){
            a[2 * i - 1] = 2 * i - 1;
        } else {
            skip;
        }
        i = i + 1; 
    }
	
	Int pos = nondet_int();
	assume(0 <= pos);
	assume(pos < alength);
	assert(a[pos] <= pos);
}
