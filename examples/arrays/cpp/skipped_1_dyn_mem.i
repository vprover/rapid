extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
    int alength = __VERIFIER_nondet_int();
    int a[alength];
 __VERIFIER_assume(0 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
    int i = 1;
    while(i <= alength) {
        if (a[2 * i - 2] > 2 * i - 2){
            a[2 * i - 2] = 2 * i - 2;
        } else {
            ;
        }
        if (a[2 * i - 1] > 2 * i - 1){
            a[2 * i - 1] = 2 * i - 1;
        } else {
            ;
        }
        i = i + 1;
    }
 int pos = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= pos);
 __VERIFIER_assume(pos < alength);
 __VERIFIER_assert(a[pos] <= pos);
}
