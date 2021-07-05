func main() {
  Int x; // input
  Int y; // input
  Int z; // input
  Int* r1 = #x;
  Int* r2 = #y;

  if(z > 0){
    while( z>0 ) {
      Int* tmp = r1;
      r1 = r2;
      r2 = tmp;
      z = z-1; 
    }
  } else {
    skip;
  }
}

(conjecture
    (=>
      (and
       (> (value_int l5 z) 0)
       (= (mod (value_int l5 z) 2) 0)  
      )
      (= (deref main_end r1) x)
    )  
)