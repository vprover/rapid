extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int length = __VERIFIER_nondet_int();
 int a[length];
 int b[length];
 __VERIFIER_assume(0 <= length);
   for (int __i = 0; __i < length; __i++) {
  a[__i] = __VERIFIER_nondet_int();
  b[__i] = __VERIFIER_nondet_int();
 }
 int r = 0;
 int i = 0;
 while (i < length) {
  if (a[i] != b[i]) {
   r = 1;
  }
  else {
   ;
  }
  i = i + 1;
 }
 int k = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= k && k < length && r != 1);
 __VERIFIER_assert(a[k] == b[k]);
}
