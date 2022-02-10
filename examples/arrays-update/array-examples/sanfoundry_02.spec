// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_02_ground.c

func main(){
    const Int[] a;
    const Int alength; 
    Int i = 2;
    Int temp;
 
    Int largest1 = a[0];
    Int largest2 = a[1];

    if (largest1 < largest2) {
        temp = largest1;
        largest1 = largest2;
        largest2 = temp;
    } else {
        skip;
    }
    while (i < alength) {
        if (a[i] >= largest1) {
            largest2 = largest1;
            largest1 = a[i];
        } else {
            skip;
        }
        if (a[i] > largest2)
        {
            largest2 = a[i];
        } else {
            skip;
        }
        i = i + 1;
    }
}

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 alength)
        (<= 0 pos)
        (< pos alength)
      )
      (<= (a pos) (largest1 main_end))
    )
  )
)

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 alength)
        (<= 0 pos)
        (< pos alength)
      )
      (or
        (<= (a pos) (largest2 main_end))
        (= (a pos) (largest1 main_end))   
      )
    )
  )
)