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
 while(i < alength) {
  a[i] = v;
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos && pos < alength);
 __VERIFIER_assert(a[pos] == v);
}
