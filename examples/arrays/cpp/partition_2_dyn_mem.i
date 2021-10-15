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
 int blength = 0;
 int c[alength];
 int clength = 0;
 int i = 0;
 while (i < alength) {
  if (a[i] >= 0) {
   b[blength] = a[i];
   blength = blength + 1;
  }
  else {
   c[clength] = a[i];
   clength = clength + 1;
  }
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < clength);
 __VERIFIER_assert(c[pos] < 0);
}
