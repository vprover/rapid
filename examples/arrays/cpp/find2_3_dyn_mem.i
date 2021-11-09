extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 int v = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= alength);
 int i = 0;
 while (i < alength && a[i] != v) {
  i = i + 1;
 }
 __VERIFIER_assume(i != alength);
 int exists = 0;
 for (int pos = 0; pos < alength; pos++) {
  exists = exists || (a[pos] == v);
 }
 __VERIFIER_assert(exists);
}
