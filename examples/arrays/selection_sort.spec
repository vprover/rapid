func main(){
  Int[] array;

  const Int n;
  Int lh = 0;
  Int rh;
  Int i;
  Int temp;

  while (lh < n) {
    rh = lh;
    i = lh + 1;
    while (i < n){ 
      if (array[i] < array[rh]){ 
        rh = i; 
      } else {
        skip;
      }
      i = i + 1;
    }

    temp = array[lh];
    array[lh] = array[rh];
    array[rh] = temp;
    lh = lh + 1;
  }
}

(axiom
  (<= 0 n)
)

(conjecture
  (forall ((k Int))
    (=>
      (and
        (<= 0 k)
        (< k (- n 1))
      )
      (<= (array main_end k) (array main_end (+ k 1)))
    )
  )
)
