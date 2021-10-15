extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int length = __VERIFIER_nondet_int();
 __VERIFIER_assume(length > 2);
 length = length * length;
 while (length > 2) {
      length = length - 1;
 }
 __VERIFIER_assert(length == 2);
}
