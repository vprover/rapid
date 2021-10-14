func main()
{
    Int i;
    Int[] a;
    const Int alength;
    const Int val2 = 3;
    const Int val1 = 7;
    const Int low=2;

    i = alength - 2; 

    while(i >= (0-1))
    {
        if(i >= 0)
        {
            a[i] = val1;
        } else {
            skip;
        }
        a[i+1] = val2;
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
            (>= (a main_end pos) low)
        )
    )
)