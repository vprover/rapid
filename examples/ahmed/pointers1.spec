func main() {
  Int a = 5;
  Int *b = #a;
  *b = 4;
}

(conjecture
    (<= (value_int main_end a) 5)  
)