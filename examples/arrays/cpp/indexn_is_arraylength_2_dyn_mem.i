extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= alength);
 int i = 0;
 while (i < alength) {
  i = i + 1;
 }
 __VERIFIER_assert(i == alength);
}
