func main() {
  Int a = 1000;
  Int *b = #a;
  Int** c = #b;
  while(a > 0){
    **c = **c - 1;
  }
}

(conjecture
    (<= (value_int main_end (deref main_end (deref main_end c))) 0)  
)