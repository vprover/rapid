//from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sorting_bubblesort_ground-1.c

func main() {
    Int[] a; 
    const Int alength;
    Int i; 
    Int temp;
    Int swapped = 1; 

    while (swapped == 1) {
        swapped = 0;
        i = 1;
        while ( i < alength ) {
            if (a[i-1] > a[i]) {
                temp = a[i];
                a[i] = a[i-1];
                a[i-1] = temp;
                swapped = 1;
            }else{
              skip;
            }
            i = i + 1;
        }
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
      )
      (<= (a main_end x) (a main_end y))
    )
  )
)
