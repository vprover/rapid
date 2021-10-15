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
 int i = 0;
 a[0] = v;
 while ((i + 1) < alength) {
  a[i + 1] = a[i] + 1;
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos && 0 <= pos + 1);
 __VERIFIER_assume(pos + 1 < alength);
 __VERIFIER_assert(a[pos] < a[pos + 1]);
}
