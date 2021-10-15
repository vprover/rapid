extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
    int i;
    int alength = __VERIFIER_nondet_int();
    int a[alength];
 __VERIFIER_assume(0 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
    int val2 = 3;
    int val1 = 7;
    int low=2;
    i = alength - 2;
    while (i >= (0-1)) {
        if (i >= 0) {
            a[i] = val1;
        }
  else {
            ;
        }
        a[i + 1] = val2;
        i = i - 1;
    }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < alength);
 __VERIFIER_assert(a[pos] >= low);
}
