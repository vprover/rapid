func main()
{
	Int[] a;
	const Int[] b;
	const Int length;

	Int i = 0;
	while(i < length && b[i] != 0)
	{
		a[i] = b[i];
		i = i + 1;
	}
}

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int length))
				(<= 0 pos)
				(< pos (value_int main_end i))
			)
			(= (select (value_arr main_end a) pos) (select (value_const_arr b) pos) )
		)
	)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int length))
				(<= 0 pos)
				(< pos (value_int main_end i))
			)
			(not (= (select (value_arr main_end a) pos) 0))
		)
	)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 (value_const_int length))
				(<= 0 pos)
				(< pos (value_int main_end i))
			)
			(not (= (select (value_const_arr b) pos) 0))
		)
	)
)

(conjecture
	(=>
		(and
			(<= 0 (value_const_int length))
			(< (value_int main_end i) (value_const_int length))
		)
		(= (select (value_const_arr b) (value_int main_end i)) 0)
	)
)
