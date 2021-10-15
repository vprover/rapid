extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 int v = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= alength);
 a[0] = v;
 int i = 1;
 while (i < alength) {
  a[i] = a[i - 1] + 1;
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos && 0 <= pos + 1);
 __VERIFIER_assume(pos + 1 < alength);
 __VERIFIER_assert(a[pos] < a[pos + 1]);
}
