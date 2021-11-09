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
 int r = alength;
 while (i < alength && r == alength) {
  if (a[i] == v) {
   r = i;
  }
  else {
   ;
  }
  i = i + 1;
 }
 __VERIFIER_assume(r < alength);
 int exists = 0;
 for (int pos = 0; pos < alength; pos++) {
  exists = exists || (a[pos] == v);
 }
 __VERIFIER_assert(exists);
}
