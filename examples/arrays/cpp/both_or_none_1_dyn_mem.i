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
 int b[alength];
 int i = 0;
 while(i < alength) {
  if (a[i] == 1) {
   b[i] = 1;
  }
  else {
   b[i] = 0;
  }
  i = i + 1;
 }
 int j = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= j);
 __VERIFIER_assume(j < alength);
 __VERIFIER_assert((a[j] == 1 && b[j] == 1) || (a[j] != 1 && b[j] == 0));
}
