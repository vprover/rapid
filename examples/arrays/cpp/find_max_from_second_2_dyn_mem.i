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
 int i = 1;
 int max = a[0];
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
 for (int k = 0; k < alength; k++) {
  exists = exists || (a[k] == max);
 }
 __VERIFIER_assert(exists);
}
