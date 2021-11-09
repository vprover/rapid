#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Const Int alength = 10;
	
	Int i = 0;
	Int j = 0;
	
	while (j < alength) {
	  if (3 == 5) {
	    i = 2;
	  } else {
	    skip;
	  }
      j = j  + 1;
	}
	assert(i == 0);
}
