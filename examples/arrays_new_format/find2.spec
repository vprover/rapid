// a new encoding of find, which is easier for the solvers, where we want to prove that
// 1) if we find a position, the element at that position is equal to v
// 2) variation of property 1)
// 3) variation of property 1)
// 4) variation of property 1)
// 5) forall positions pos between 0 and i, A[pos] is different from v

func main()
{
	const Int[] a;
	const Int alength;
	const Int v;

	Int i = 0;
	while (i < alength && a[i] != v)
	{
		i = i + 1;
	}
}

(conjecture
	(=>
		(and
			(<= 0 (value_const_int alength))
			(not (= (value_int main_end i) (value_const_int alength)))
		)
		(= 
		    (select (value_const_arr a) (value_int main_end i)) 
		    (value_const_int v)
		)
	)
)

(conjecture
	(=>
		(and
			(<= 0 (value_const_int alength))
			(< (value_int main_end i) (value_const_int alength))
		)
		(= 
		    (select (value_const_arr a) (value_int main_end i)) 
		    (value_const_int v)
		)	
	)
)

(conjecture
	(=>
		(and
			(<= 0 (value_const_int alength))
			(not (= (value_int main_end i) (value_const_int alength)))
		)
		(exists ((pos Int))
			(= 
			    (select (value_const_arr a) pos)
			    (value_const_int v)
			)
		)
	)
)

(conjecture
	(=>
		(and
			(<= 0 (value_const_int alength))
			(< (value_int main_end i) (value_const_int alength))
		)
		(exists ((pos Int))
			(= 
			    (select (value_const_arr a) pos)
			    (value_const_int v)
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
				(< pos (value_int main_end i))
			)
			(not 
			    (= 
			        (select (value_const_arr a) pos) 
			        (value_const_int v)
			    )
			)
		)
	)
)
