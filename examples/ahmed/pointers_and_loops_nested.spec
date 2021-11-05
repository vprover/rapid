func main() {
  Int mult = 0;
  Int* multPointer = #mult;
  Int a;
  Int b;

  while(a > 0){
    Int bInLoop = b;
    while(bInLoop > 0){
      *multPointer = *multPointer + 1;
      bInLoop = bInLoop - 1;
    }
    a = a - 1;
  }
}

(conjecture
    (=>
        (and
            (> (value_int (l7 zero) a) 0)
            (> (value_int (l7 zero) b) 0)
        )
        (= 
           (value_int main_end mult) 
           (* (value_int (l7 zero) a) (value_int (l7 zero) b))
        )  
    )
)