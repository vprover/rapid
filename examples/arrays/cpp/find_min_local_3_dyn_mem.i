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
 int i = 0;
 int m = 0;
 while (i < alength) {
  if (a[i] < a[m]) {
   b[i] = a[i];
   blength = blength + 1;
   m = i;
  }
  else {
   ;
  }
  i = i + 1;
 }
 int j = __VERIFIER_nondet_int();
 int k = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= j && 0 <= k && j <= k && k < blength);
 __VERIFIER_assert(b[k] <= b[j]);
}
