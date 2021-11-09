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
 int i = 0;
 int j = 0;
 while (i < blength) {
  a[i] = b[j];
  i = i + 1;
  j = j + 1;
 }
 int k = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= k);
 __VERIFIER_assume(k < blength);
 __VERIFIER_assert(a[k] == b[k]);
}
