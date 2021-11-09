extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 int al12[alength];
 __VERIFIER_assume(0 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  int value = __VERIFIER_nondet_int();
  a[__i] = value;
  al12[__i] = value;
 }
 int i = 0;
 while (i < alength) {
  a[i] = a[i] + 1;
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < alength);
 __VERIFIER_assert(a[pos] == al12[pos] + 1);
}
