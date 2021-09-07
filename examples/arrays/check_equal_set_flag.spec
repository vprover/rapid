// check whether two arrays are the same at each position. If not, set the flag r to 1.
// Prove that if flag was not set to 1, then arrays are equal.
// similar to all of the following examples:
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_compare_true-unreach-call_ground.c
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_strcmp_true-unreach-call_ground.c
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_password_true-unreach-call_ground.c

func main()
{
  const Int[] a;
  const Int[] b;
  const Int length;

  Int r = 0;
  Int i = 0;
  while(i < length)
  {
    if(a[i] != b[i])
    {
      r = 1;
    }
    else
    {
      skip;
    }
    i = i + 1;
  }
}

(axiom
  (<= 0 length)
)


(conjecture
  (=>
    (and
      (<= 0 length)
      (= (r main_end) 1)
    )
    (exists ((k Int))
      (not 
        (= (a k) (b k))
      )
    )
  )
)

(conjecture
  (forall ((k Int))
    (=>
      (and
        (<= 0 k)
        (< k length)
        (<= 0 length)
        (not (= (r main_end) 1))
      )
      (= (a k)(b k))
    )
  )
)
