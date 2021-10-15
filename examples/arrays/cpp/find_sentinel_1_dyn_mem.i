extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int j = __VERIFIER_nondet_int();
 int v = __VERIFIER_nondet_int();
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 __VERIFIER_assume(0 <= alength);
 __VERIFIER_assume(0 <= j);
 __VERIFIER_assume(j < alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 int i = 0;
 a[j] = v;
 while (i < alength && a[i] != v) {
  i = i + 1;
 }
 __VERIFIER_assert(i <= j);
}
