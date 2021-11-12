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

(assert
  (<= 2 alength)
)

(conjecture
  (forall ((k Int))
    (=>
      (and
        (<= 0 k)
        (< k (- alength 1))
      )
      (<= (a main_end k) (a main_end (+ k 1)))
    )
  )
)
