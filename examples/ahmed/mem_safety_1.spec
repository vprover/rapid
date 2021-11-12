func main() {

  Int a;
  Int c = 5;
  Int* ptr = #c;

  while(a > 0){
    *ptr = 2;
    Int b = 3;
    ptr = #b;
  }
  *ptr = 1;
}

(conjecture
  true 
)