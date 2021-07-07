func main() {
  Int a = 5;
  Int b = 2;
  Int* c; 

  if(a < 6){
    c = #b;
  } else {
    c = #a;
  }
  *c = *c + 1;
 }


(conjecture
    (= (value_int main_end b) 3)  
)