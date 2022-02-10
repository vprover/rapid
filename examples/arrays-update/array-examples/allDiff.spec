// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_allDiff2_ground.c
// note there is an error in the original example since r is always one


func main(){
    const Int[] a; 
    const Int alength;
    Int r = 1;
    Int i = 1; 
    Int j = 0;

    while (i < alength && r == 1) {
        j = i - 1;
        while (j >= 0 && r == 1) {
            if (a[i] != a[j]) {
                r = 1;
            } else {
                r = 0; 
            }
            j = j - 1;
        }
        i = i + 1; 
    }
}

(conjecture
  (forall ((x Int)(y Int))
    (=>
      (and
        (<= 0 alength)
        (<= 0 x)
        (<= 0 y)
        (< x alength)
        (< y alength)
        (= y (+ x 1))
        (= (r main_end) 1)
      )
      (not (= (a x) (a y)))
    )
  )
)

