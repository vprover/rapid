extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int length = __VERIFIER_nondet_int();
 int b[length];
 __VERIFIER_assume(0 <= length);
 for (int __i = 0; __i < length; __i++) {
  b[__i] = __VERIFIER_nondet_int();
 }
 int a[length];
 int i = 0;
 while(i < length) {
  a[i] = b[length - 1 - i];
  i = i + 1;
 }
 int j = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= j);
 __VERIFIER_assume(j < length);
 __VERIFIER_assert(a[j] == b[(length - 1) - j]);
}
