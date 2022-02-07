struct Test1 {
  Int member;
  Int member2;
};

func main() {
  Test1 a;
  Int rc = 0;
  Int result;
  Int x;
  Int* y;
  y = malloc();
  a.member = 2;
  x = a.member + x + x + x;
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
  (>= (value_int main_end result) 0)
)