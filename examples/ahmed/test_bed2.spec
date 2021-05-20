func main() {
  Int res = 0;
  const Int[] arr;
  Int j = 0;
  while(j < 2){
    if(arr[j] == 2){
      res = 1;
    } else {
      skip;
    }
    j = j + 1;
  }
}

(conjecture
   (=> 
     (= (res main_end) 1) 
     (exists ((k Int))
       (= (arr k) 2)
     )
   )
)