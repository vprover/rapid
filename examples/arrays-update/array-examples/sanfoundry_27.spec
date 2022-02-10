// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_27_ground.c

func main(){
    const Int[] a; 
    const Int alength;
    Int largest = a[0];
    Int i = 1; 
    while (i < alength)
    {
      if (largest < a[i]) {
        largest = a[i];
      }else {
        skip;
      }
    }
}

(conjecture
  (forall ((x Int))
    (=>
      (and
        (<= 0 alength)
        (<= 0 x)
        (< x alength)
      )
      (<= (a x) (largest main_end))
    )
  )
)
