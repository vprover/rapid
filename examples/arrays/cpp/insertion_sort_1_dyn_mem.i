extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int i;
 int j = 1;
 int pivot;
 int alength = __VERIFIER_nondet_int();
 int a[alength];
 __VERIFIER_assume(2 <= alength);
 for (int __i = 0; __i < alength; __i++) {
  a[__i] = __VERIFIER_nondet_int();
 }
 while(j < alength) {
  pivot = a[j];
  i = j - 1;
  while(i >= 0 && a[i] > pivot) {
   a[i + 1] = a[i];
   i = i -1;
  }
  a[i + 1] = pivot;
  j = j + 1;
 }
 int k = __VERIFIER_nondet_int();
 __VERIFIER_assume(0 <= k);
 __VERIFIER_assume(k < alength - 1);
 __VERIFIER_assert(a[k] <= a[k + 1]);
}
