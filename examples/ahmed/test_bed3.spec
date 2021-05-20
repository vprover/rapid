func main() {
  Int rc = 0;
  Int result;
  Int x;
  if(x < 0){
    if(rc == 0){
      result = 0 - x;
      rc = 1;
    } else {
      skip;
    }
  } else {
    if(rc == 0){
      result = x;
      rc = 1;
    } else {
      skip;
    }
  }
}

(conjecture
  (>= (result main_end) 0)
)