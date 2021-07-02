func main() {
  Int a = 1000;
  Int *b = #a;
  Int** c = #b;
  while(a > 0){
    **c = **c - 1;
  }
  //val l4 (deref l4 d) = 2
  //d = #c; deref l4 d = c
  //Int[] a;
  //Int[] b;
  //b[10] = 3; //value_arr l9 b = store (value_arr l8 b) 10 3
  //a[2] = 10;
  //a[5] = 7;
  //Int temp = a[2]; //value_int l12 temp = select (value_arr l11 a) 2
  //a[2] = a[5];
  //a[5] = temp;
}

(conjecture
    (<= (value_int main_end (deref main_end b)) 0)  
)