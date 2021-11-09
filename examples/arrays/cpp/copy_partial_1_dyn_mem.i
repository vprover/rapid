extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = 0;
 int blength = __VERIFIER_nondet_int();
 int b[blength];
 int a[blength];
 for (int __i = 0; __i < blength; __i++) {
  b[__i] = __VERIFIER_nondet_int();
 }
 int k = __VERIFIER_nondet_int();
 __VERIFIER_assume(k <= blength);
 __VERIFIER_assume(0 <= blength);
 while (alength < k) {
  a[alength] = b[alength];
  alength = alength + 1;
 }
 int j = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= j);
 __VERIFIER_assume(j < k);
 __VERIFIER_assert(a[j] == b[j]);
}
