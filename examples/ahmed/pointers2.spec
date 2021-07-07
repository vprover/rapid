func main() {
  Int a = 5;
  Int *b = #a;
  Int* c = b;
  *c = 2;
}

(conjecture
    (= (value_int main_end a) 2)  
)