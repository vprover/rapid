// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sorting_selectionsort_ground-1.c

func main(){
  Int[] a;
  const Int alength;
  Int i = 0;
  Int k = i + 1;
  Int m = i;
  Int temp;

  while (i < alength) {
      k = i + 1;
      m = i;
      while (k < alength) {
        if (a[k] < a[m]) {
            m = k;
        } else {
          skip;
        }
        k = k+1;
      }
      if ( m != i ) {
        temp = a[m];
        a[m] = a[i];
        a[i] = temp;
      } else {
        skip;
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
        (< x y)
        (< x alength)
        (< y alength)
        (= y (+ x 1))
      )
      (<= (a main_end x) (a main_end y))
    )
  )
)


// intermediate properties that need be translated to trace logic
//   for ( x = 0 ; x < i ; x++ ) {
//        for ( y = x + 1 ; y < i ; y++ ) {
//       __VERIFIER_assert(  a[x] <= a[y]  );
//        }
//    }
//    for ( x = i+1 ; x < N ; x ++ ) {
//       __VERIFIER_assert(  a[x] >= a[i]  );
//    }

   