func main() {
  Int x; // input
  Int y; // input
  Int z; // input
  Int r1 = x;
  Int r2 = y;

  while( z>0 ) {
    Int tmp = r1;
    r1 = r2;
    r2 = tmp;
    z = z-1; 
  }
}

(conjecture
    (or
      (= (r1 main_end) (x main_end))
      (= (r1 main_end) (y main_end))     
    )  
)