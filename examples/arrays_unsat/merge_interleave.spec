func main()
{
	const Int[] a;
  const Int[] b;
  Int[] c;
	const Int alength;

	Int i = 0;
	while(i < alength)
	{
    c[i * 2] = a[i];
    c[i * 2 + 1] = b[i];
		i = i + 1;
	}
}

(axiom
  (<= 0 alength)
)


(conjecture
   (forall ((pos Int))
      (=>
        (and
          (<= 0 alength)
          (<= 0 pos)
          (< pos alength)
        )
        (= (c main_end (+ (* pos 2) 1)) (a pos))
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
        (= (c main_end (* pos 2)) (b pos))
      )
   )
)

(conjecture
   (forall ((pos Int))
      (exists ((j Int))
        (=>
          (and
            (<= 0 alength)
            (<= 0 pos)
            (< pos alength)
          )
          (or
            (= (c main_end pos) (* (a j) 2))
            (= (c main_end pos) (b j))
          )
        )
      )
   )
)