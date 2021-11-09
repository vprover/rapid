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
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < length);
 int bl8 = b[pos];
 int i = 0;
 while(i < length) {
  int current = a[i];
  a[i] = b[i];
  b[i] = current;
  i = i + 1;
 }
 __VERIFIER_assert(a[pos] == bl8);
}
