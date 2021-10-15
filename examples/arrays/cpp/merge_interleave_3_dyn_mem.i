extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a[2 * alength];
 int b[2 * alength];
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
 __VERIFIER_assume(pos < alength * 2);
 int exists = 0;
 for (int j = 0; j < 2 * alength; j++){
  exists = exists || (c[pos] == a[j] || c[pos] == b[j]);
 }
 __VERIFIER_assert(exists);
}
