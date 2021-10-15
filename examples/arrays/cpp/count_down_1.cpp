#include <stdlib.h>
#include "seahorn/seahorn.h"
#include "rapid.h"

func main()
{
	Int length = nondet_int();
	assume(length > 2);
	length = length * length;

	while (length > 2) {
      length = length - 1;
	}
	
	assert(length == 2);
}
