//from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_partial_init_ground.c

func main()
{
	const Int[] a;
	const Int length;
   const Int[] b;
   Int[] c;

	Int i = 0;
   Int j = 0;
	while (i < length){
      if (a[i] == b[i]){
         c[j] = i;
         j = j + 1; 
      }else {
         skip;
      }
		i = i + 1;
	}
}

(axiom
  (<= 0 length)
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (j main_end))
            (<= 0 length)
         )
         (>= (c main_end pos) pos)
      )
   )
)

(conjecture
   (forall ((pos Int))
      (=>
         (and
            (<= 0 pos)
            (< pos (j main_end))
            (<= 0 length)
         )
         (<= (c main_end pos) (+ pos (- (i main_end) (j main_end))))
      )
   )
)