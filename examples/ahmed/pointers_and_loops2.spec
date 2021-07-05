func main() {
  Int a = 1000;
  Int *b = #a;
  while(*b > 0){
    a = a - 1;
  }
}

(conjecture
    (<= (value_int main_end a) 0)  
)