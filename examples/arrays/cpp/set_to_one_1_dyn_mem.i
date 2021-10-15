extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 __VERIFIER_assume(0 < alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 int i = 0;
 int j = 0;
 while(i < alength) {
  i = i + 1;
  j = 1;
 }
 __VERIFIER_assert(j == 1);
}
