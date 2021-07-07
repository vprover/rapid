// Harder versions of some of the properties from partition-example
// 1) each element in b is a copy of some element in a, which fulfils the range-bounds of a
// 2) each element in c is a copy of some element in a, which fulfils the range-bounds of a
// 3) for each element in a, which is greater or equal 0, there exists a copy of that element in b, which fulfils the range-bounds of b
// 4) for each element in a, which is smaller than 0, there exists a copy of that element in c, which fulfils the range-bounds of c
// 5) for each element in a, either there exists a copy of that element in b, which fulfils the range-bounds of b, or there exists a copy of that element in c, which fulfils the range-bounds of c

func main()
{
  const Int[] a;
  const Int alength;

  Int[] b;
  Int blength = 0;
  Int[] c;
  Int clength = 0;

	Int i = 0;
	while(i < alength)
	{
      if(a[i] >= 0)
      {
        b[blength] = a[i];
        blength = blength + 1;
      }
      else
      {
        c[clength] = a[i];
        clength = clength + 1;
      }
      i = i + 1;
	}
}

(axiom
  (forall ((it Nat))
    (<= 
      (value_int (l19 it) blength)
      (value_int (l19 it) i) 
    )
  )
)
(axiom
  (forall ((it Nat))
    (<= 
      (value_int (l19 it) clength)
      (value_int (l19 it) i) 
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
      (exists ((pos2 Int))
        (and
          (<= 0 pos2)
          (< pos2 (value_const_int alength))
          (= (select (value_arr main_end b) pos) (select (value_const_arr a) pos2))
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
        (< pos (value_int main_end clength))
      )
      (exists ((pos2 Int))
        (and
          (<= 0 pos2)
          (< pos2 (value_const_int alength))
          (= (select (value_arr main_end c) pos) (select (value_const_arr a) pos2))
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
        (<= 0 (select (value_const_arr a) pos))
      )
      (exists ((pos2 Int))
        (and
          (<= 0 pos2)
          (< pos2 (value_int main_end blength))
          (= (select (value_arr main_end b) pos2) (select (value_const_arr a) pos))
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
        (< (select (value_const_arr a) pos) 0)
      )
      (exists ((pos2 Int))
        (and
          (<= 0 pos2)
          (< pos2 (value_int main_end clength))
          (= (select (value_arr main_end c) pos2) (select (value_const_arr a) pos))
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
      )
      (or
        (exists ((pos2 Int))
          (and
            (<= 0 pos2)
            (< pos2 (value_int main_end blength))
            (= (select (value_arr main_end b) pos2) (select (value_const_arr a) pos))
          )
        )
        (exists ((pos2 Int))
          (and
            (<= 0 pos2)
            (< pos2 (value_int main_end clength))
            (= (select (value_arr main_end c) pos2) (select (value_const_arr a) pos))
          )
        )
      )
    )
  )
)