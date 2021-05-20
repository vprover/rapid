func main() {
  Int i;
  Int k;
  Int n;
  Int return;
  Int rc = 0;
  if (!((i==0) && (k==0) && (n>0))){
    if(rc == 0){
      rc = 1;
      return = 0;
    } else {
      skip;
    }
  } else {
    skip;
  }
  while (i < n) {
    i = i  + 1;
    k = k + 1;
  }
}

(conjecture
  (=> 
    (= (rc main_end) 0)
    (and
      (= (i main_end) (k main_end))
      (= (k main_end) (n main_end))
    )
  )
)
