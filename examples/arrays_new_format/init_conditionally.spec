func main()
{
	const Int[] a;
	const Int[] b;
	Int[] c;

	const Int length;

	Int i = 0;
	Int clength = 0;
	while(i < length)
	{
		if (a[i] == b[i])
		{
			c[clength] = i;
			clength = clength + 1;
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
				(<= 0 pos)
				(< pos (value_int main_end clength))
				(<= 0 (value_const_int length))
			)
			(=
				(select (value_const_arr a) (select (value_arr main_end c) pos))
				(select (value_const_arr b) (select (value_arr main_end c) pos))
			)
		)
	)
)

(axiom
	(forall ((it Nat))
		(<= (value_int (l11 it) clength) (value_int (l11 it) i))
	)
)

(conjecture
	(forall ((pos Int))
		(=>
			(and
				(<= 0 pos)
				(< pos (value_int main_end clength))
				(<= 0 (value_const_int length))
			)
			(<= pos (select (value_arr main_end c) pos))
		)
	)
)
