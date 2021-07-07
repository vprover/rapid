// for each position p: if a[p] is 1, set b[p] to 1, otherwise set it to zero.
// Prove that either both a[p] is 1 and b[p] is 1, or both a[p] is not 1 and b[p] is zero
// similar to https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_running_true-unreach-call.c
// but simplified

func main()
{
  const Int[] a;
  const Int alength;
  Int[] b;

  Int i = 0;
  while(i < alength)
  {
    if (a[i] == 1)
    {
      b[i] = 1;
    }
    else
    {
      b[i] = 0;
    }
    i = i + 1;
  }
}


(conjecture
  (forall ((j Int))
    (=>
      (and
        (<= 0 j)
        (< j (value_const_int alength))
        (<= 0 (value_const_int alength))
      )
      (or
        (and
          (= (select (value_const_arr a) j) 1)
          (= (select (value_arr main_end b) j) 1)
        )
        (and
          (not (= (select (value_const_arr a) j) 1) )
          (= (select (value_arr main_end b) j) 0)
        )
      )
    )
  )
)
