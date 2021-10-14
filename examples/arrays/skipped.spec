
func main()
{
    Int[] a;
    const Int alength; 
    Int i = 1;

    while(i <= alength) {
        if(a[2*i-2] > 2*i-2){
            a[2*i-2] = 2*i-2;
        } else {
            skip;
        }
        if(a[2*i-1] > 2*i-1){
            a[2*i-1] = 2*i-1;
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
                (>= alength 0)
                (<= 0 pos)
                (< pos alength)
            )
            (<= (a main_end pos) pos)
        )
    )
)