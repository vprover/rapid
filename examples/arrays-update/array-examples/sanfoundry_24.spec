// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_24-1.c

func main(){
    const Int[] a;
    const Int alength; 
    Int[] even;
    Int[] odd;
   
    Int i = 0;
    Int evenlength = 0;
    while (i < alength)
    {
        if ((a[i] mod 2) == 0){
            even[evenlength] = a[i];
            evenlength = evenlength + 1; 
        } else {
            skip;
        }
        i = i + 1; 
    }

    Int oddlength = 0;
    i = 0;
    while (i < alength)
    {
        if ((a[i] mod 2) != 0){
            odd[oddlength] = a[i];
            oddlength = oddlength + 1; 
        } else {
            skip;
        }
        i = i + 1; 
    }
}

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 alength)
        (<= 0 pos)
        (< pos (evenlength main_end))
      )
      (= (mod (even main_end pos) 2) 0)
    )
  )
)

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 alength)
        (<= 0 pos)
        (< pos (oddlength main_end))
      )
      (not (= (mod (odd main_end pos) 2) 0))
    )
  )
)