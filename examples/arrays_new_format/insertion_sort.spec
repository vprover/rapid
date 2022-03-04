func main()
{
  Int i;
  Int j = 1;
  Int pivot;

  const Int alength;
  Int[] a;

  while(j < alength)
  {
    pivot = a[j];
    i = j - 1;
    while(i >= 0 && a[i] > pivot)
    {
      a[i + 1] = a[i];
      i = i -1;
    }
    a[i + 1] = pivot;
    j = j + 1;
  }
}

(axiom
  (<= 2 (value_const_int alength))
)

(conjecture
  (forall ((k Int))
    (=>
      (and
        (<= 0 k)
        (< k (- (value_const_int alength) 1))
      )
      (<= (select (value_arr main_end a) k) (select (value_arr main_end a) (+ k 1)))
    )
  )
)
