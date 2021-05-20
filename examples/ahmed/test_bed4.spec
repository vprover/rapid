func main() {
  const Int[] arr;
  const Int len;
  const Int item;
  Int i = 0;
  Int res;
  Int rc = 0;
  while(i < len){
    if(arr[i] == item){
      if(rc==0){
        rc=1;
        res=1;
      } else {
        skip;
      }
    } else {
      skip;
    }
    i = i + 1;
  }
  if(rc == 0){
    res = 0;
  } else {
    skip;
  }
}

(conjecture
   (=> (= (res main_end) 0) (forall ((j Int))
                               (=> (and (>= j 0) (< j len)) (not (= (arr j) item)))))
)