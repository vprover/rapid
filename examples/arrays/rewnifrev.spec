func main()
{
    Int i;
    Int[] a;
    const Int alength;
    const Int val2 = 3;
    const Int val1 = 7;
    const Int low=2;

    i = alength - 1; 

    while(i >= 0)
    {
        if((i-1) >= 0) {
            a[i-1] = i-2;
        }
        else {
            skip;
        }
        a[i] = i;
        i = i - 1; 
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