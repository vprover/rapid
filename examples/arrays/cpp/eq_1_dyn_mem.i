extern void __VERIFIER_error (void);
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int();
void __VERIFIER_assert(int cond) { if(!(cond)) { ERROR: __VERIFIER_error(); } }
void main()
{
 int alength = 10;
 int i = 0;
 int j = 0;
 while (j < alength) {
   if (3 == 5) {
     i = 2;
   } else {
     ;
   }
      j = j + 1;
 }
 __VERIFIER_assert(i == 0);
}
