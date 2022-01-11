#ifndef ___RAPID___
#define ___RAPID___
     
extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);

#define assume __VERIFIER_assume
#define sassert(X) (void)((X) || (__VERIFIER_error (), 0))

#define func void /* Main function */
#define Int int

#ifndef __cplusplus
#include <stdbool.h>
#endif
#define Bool bool

#define skip
#define const
#define Const

#ifndef assert
#define assert(v) if (!(v)) __VERIFIER_error();
#endif
#ifndef static_assert
#define static_assert(v) assert(v)
#endif
#ifndef assume
#define assume(v) __VERIFIER_assume(v)
#endif
#ifndef nondet_int
extern int __VERIFIER_nondet_int();
#define nondet_int() __VERIFIER_nondet_int();
#endif

#endif