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
 int all = 1;
 for (int k = 0; k < alength; k++) {
  all = all && (a[k] > 0);
 }
 __VERIFIER_assume(all);
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
 __VERIFIER_assert(min == 0);
}
