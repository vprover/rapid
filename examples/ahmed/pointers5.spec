func main() {
  Int a;
  Int b;
  Int* c; 

  if(a < b){
    c = #b;
  } else {
    c = #a;
  }
  *c = *c + 1;
 }


(conjecture
  (or
    (= (value_int main_end b) (+ (value_int l6 b) 1))
    (= (value_int main_end a) (+ (value_int l6 a) 1))      
  )
)