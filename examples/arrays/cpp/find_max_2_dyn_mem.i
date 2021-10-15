extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 __VERIFIER_assume(0 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 int k1 = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= k1);
 __VERIFIER_assume(k1 < alength);
 __VERIFIER_assume(0 <= a[k1]);
 int i = 0;
 int max = 0;
 while (i < alength) {
  if (a[i] > max) {
   max = a[i];
  }
  else {
   ;
  }
  i = i + 1;
 }
 int exists = 0;
 for (int k2 = 0; k2 < alength; k2++) {
  exists = exists || (a[k2] == max);
 }
 __VERIFIER_assert(exists);
}
