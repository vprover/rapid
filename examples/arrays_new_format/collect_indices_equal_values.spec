// generate a new array b containing all indices where the arrays a1 and a2 have the same value.
// Properties:
// 1) Each element of b corresponds to a position in a1/a2.
// 2) For each element of b, the elements in a1 and a2 at the corresponding index are the same.
// 3) If the elements in a1 and a2 are the same at position pos, then there exists an element in b with value pos.
// 4) If the elements in a1 and a2 are the same at position pos, then there exists an element in b with value pos, and that element is between 0 and blength.

func main()
{
  const Int[] a1;
  const Int[] a2;
  const Int alength;

  Int[] b;
  Int blength = 0;

	Int i = 0;
	while(i < alength)
	{
    if(a1[i] == a2[i])
    {
      b[blength] = i;
      blength = blength + 1;
    }
    else
    {
      skip;
    }
    i = i + 1;
	}
}

(conjecture
   (forall ((pos Int))
      (=>
        (and
          (<= 0 (value_const_int alength))
          (<= 0 pos)
          (< pos (value_int main_end blength))
        )
        (and
          (<= 0 (select (value_arr main_end b) pos))
          (< 
            (select (value_arr main_end b) pos) 
            (value_const_int alength))
        )
      )
   )
)

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 (value_const_int alength))
        (<= 0 pos)
        (< pos (value_int main_end blength))
      )
      (= 
        (select (value_const_arr a1) (select (value_arr main_end b) pos)) 
        (select (value_const_arr a2) (select (value_arr main_end b) pos))
      )
    )
  )
)

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 (value_const_int alength))
        (<= 0 pos)
        (< pos (value_const_int alength))
        (= 
          (select (value_const_arr a1) pos) 
          (select (value_const_arr a2) pos)
        )
      )
      (exists ((pos2 Int))
        (and
          (= (select (value_arr main_end b) pos2) pos)
        )
      )
    )
  )
)

(conjecture
  (forall ((pos Int))
    (=>
      (and
        (<= 0 (value_const_int alength))
        (<= 0 pos)
        (< pos (value_const_int alength))
        (= 
          (select (value_const_arr a1) pos) 
          (select (value_const_arr a2) pos)
        )
      )
      (exists ((pos2 Int))
        (and
          (<= 0 pos2)
          (< pos2 (value_int main_end blength))
          (= (select (value_arr main_end b) pos2) pos)
        )
      )
    )
  )
)