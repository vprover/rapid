extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int blength = __VERIFIER_nondet_int();
 int b[blength];
 __VERIFIER_assume(0 <= blength);
 for (int __i = 0; __i < blength; __i++) {
  b[__i] = __VERIFIER_nondet_int();
 }
 int a[blength];
 int alength = 0;
 int i = 0;
 while (i < blength) {
  __VERIFIER_assume(alength <= i);
  a[i] = b[i];
  alength = alength + 1;
  i = i + 1;
 }
 int j = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= j);
 __VERIFIER_assume(j < alength);
 __VERIFIER_assert(a[j] == b[j]);
}
