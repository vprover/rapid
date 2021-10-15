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
 __VERIFIER_assume (0 <= k1 && k1 < alength && a[k1] <= 0);
 int i = 0;
 int min = 0;
 while (i < alength) {
  if (a[i] < min) {
   min = a[i];
  }
  else {
   ;
  }
  i = i + 1;
 }
 int exists = 0;
 for (int k2 = 0; k2 < alength; k2++) {
  exists = exists || (a[k2] == min);
 }
 __VERIFIER_assert(exists);
}
