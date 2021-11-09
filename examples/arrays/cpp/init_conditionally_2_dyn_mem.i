extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int length = __VERIFIER_nondet_int();
 int a[length];
 int b[length];
 for (int __i = 0; __i < length; __i++) {
  a[__i] = __VERIFIER_nondet_int();
  b[__i] = __VERIFIER_nondet_int();
 }
 int c[length];
 __VERIFIER_assume(0 <= length);
 int i = 0;
 int clength = 0;
 while(i < length) {
  __VERIFIER_assume(clength <= i);
  if (a[i] == b[i]) {
   c[clength] = i;
   clength = clength + 1;
  }
  else {
   ;
  }
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos && pos < clength);
 __VERIFIER_assert(pos <= c[pos]);
}
