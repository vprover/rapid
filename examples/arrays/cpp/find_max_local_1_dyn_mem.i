extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 __VERIFIER_assume(1 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 int b[alength];
 b[0] = a[0];
 int blength = 1;
 int i = 1;
 int m = 0;
 while (i < alength) {
  if (a[i] > a[m]) {
   b[blength] = a[i];
   blength = blength + 1;
   m = i;
  }
  else {
   ;
  }
  i = i + 1;
 }
 int k = __VERIFIER_nondet_int();
 __VERIFIER_assume(1 <= alength);
 __VERIFIER_assume(0 <= k && k < alength);
 int all = 1;
 for (int l = 0; l < k; l++) {
  all = all && (a[l] < a[k]);
 }
 __VERIFIER_assume(all);
 int exists = 0;
 for (int j = 0; j < blength; j++) {
  exists = exists || (a[k] == b[j]);
 }
 __VERIFIER_assert(exists);
}
