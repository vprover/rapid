// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/standard_copyInitSum3_ground.c
// Note we use a symbolic value v instead of a some integer constant.


func main()
{
	Int[] a;
	const Int alength;
	const Int v;
    Int[] b; 

	Int i = 0;
	while(i < alength)
	{
		a[i] = v;
		i = i + 1;
	}

    i = 0; 
    while(i < alength)
	{
		b[i] = a[i];
		i = i + 1;
	}

    i = 0; 
    while(i < alength)
	{
		b[i] = b[i] + i;
		i = i + 1;
	}

    i = 0; 
    while(i < alength)
	{
		b[i] = b[i] - a[i];
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
            (<= 0 pos)
            (< pos alength)
            (<= 0 alength)
         )
         (= (b main_end pos) pos)
      )
   )
)
