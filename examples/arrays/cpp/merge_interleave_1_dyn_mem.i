extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 int b[alength];
 __VERIFIER_assume(0 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
  b[__i] = __VERIFIER_nondet_int();
 }
 int c[2 * alength];
 int i = 0;
 while (i < alength) {
  c[i * 2] = a[i];
  c[i * 2 + 1] = b[i];
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < alength);
 __VERIFIER_assert(c[pos * 2] == a[pos]);
}
