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
 while (i < length && b[i] != 0) {
  a[i] = b[i];
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < i);
 __VERIFIER_assert(a[pos] != 0);
}
