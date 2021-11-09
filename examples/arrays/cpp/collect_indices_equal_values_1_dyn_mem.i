extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = __VERIFIER_nondet_int();
 int a1[alength];
 int a2[alength];
 __VERIFIER_assume(0 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a1[__i] = __VERIFIER_nondet_int();
  a2[__i] = __VERIFIER_nondet_int();
 }
 int b[alength];
 int blength = 0;
 int i = 0;
 while(i < alength) {
  if (a1[i] == a2[i]) {
   b[blength] = i;
   blength = blength + 1;
  }
  else {
   ;
  }
  i = i + 1;
 }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < blength);
 __VERIFIER_assert(0 <= b[pos] && b[pos] < alength);
}
