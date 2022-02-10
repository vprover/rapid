// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_compare_ground.c
// note same example as password https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_password_ground.c

func main() {
  const Int[] a;
  const Int length; 
  const Int[] b;
  Int i = 0;
  Int rv = 1;
	
  while (i < length) {
    if (a[i] != b[i]) {
      rv = 0;
    } else {
      skip;
    }
    i = i + 1;
  }
}


(conjecture
  (forall ((x Int))
    (=>
      (and
        (<= 0 length)
        (<= 0 x)
        (< x length)
        (= (rv main_end) 1)
      )
      (= (a x) (b x))
    )
  )
)
