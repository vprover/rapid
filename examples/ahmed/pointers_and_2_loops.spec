func main() {
  Int a = 1000;
  Int b;
  Int* aPtr = #a;
  Int* bPtr = #b;

  *bPtr = a;

  while(a > 0){
    *aPtr = *aPtr - 1;
  }

  while(a < *bPtr){
    a = a + 1;
  }
}


(conjecture
  (forall ((it Nat))
      (= (value_int (l9 (s it)) a) (value_int (l9 it) a)) 
  )
)


(conjecture
  (= 
     (value_int main_end (deref main_end aPtr)) 
     1000
  )  
)

(conjecture
  (and
    (= 
      (value_int (l9 zero) (deref (l9 zero) aPtr)) 
      1000
    )
    (= 
      (value_int (l9 zero) b) 
      1000
    )
  )  
)