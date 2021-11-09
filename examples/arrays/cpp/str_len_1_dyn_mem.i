extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int length = __VERIFIER_nondet_int();
 int a[length];
 __VERIFIER_assume(0 <= length);
 for (int __i = 0; __i < length; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < length);
 __VERIFIER_assume(a[pos] == 0);
 int i = 0;
 while (a[i] != 0) {
  i = i + 1;
 }
 int j = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= j);
 __VERIFIER_assume(j < i);
 __VERIFIER_assert(a[j] != 0);
}
