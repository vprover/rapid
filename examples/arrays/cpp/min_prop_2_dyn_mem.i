extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int blength = __VERIFIER_nondet_int();
 int b[blength];
 __VERIFIER_assume(0 <= blength);
 for (int __i = 0; __i < blength; __i++) {
  b[__i] = __VERIFIER_nondet_int();
 }
 int a[blength];
 int i = 0;
 while (i < blength) {
  if (b[i] < 0) {
   a[i] = b[i];
  }
  else {
   a[i] = 0;
  }
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < blength);
 __VERIFIER_assert(a[pos] == 0 || a[pos] == b[pos]);
}
