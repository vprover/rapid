#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"
// example which shows that we need the requirement that array-lengths are nonnegative: 
// If we remove the precondition "0 <= alength", then neither the standard-encoding nor 
// the timepoint encoding is able to prove the postcondition "i == alength".
// In particular, the following property is not valid:
// (conjecture
// 		 (= (i main_end) alength)
// )

func main()
{
	Const Int alength = nondet_int();
	assume(0 <= alength);
	Int i = 0;

	while (i < alength) {
		i = i + 1;
	}
	assert(i >= alength);
}
