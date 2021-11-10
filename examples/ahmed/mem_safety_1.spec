func main() {

  Int a;
  Int c = 5;
  Int* ptr = #c;
  Int* ptr2;
  *ptr2 = *ptr;

  if(a > 0){
    Int b = 3;
    ptr = #b;
  }  else {
    skip;
  } 
  *ptr = 1;
}

(conjecture
  true 
)