// similar to copy, but keeps track of the size of a and asserts the property with respect to the size of a

func main()
{
	Int[] a;
	const Int[] b;
	const Int blength;

	Int alength = 0;
	Int i = 0;
	while(i < blength)
	{
		a[i] = b[i];
		alength = alength + 1;
		i = i + 1;
	}
}

(axiom
	(forall ((it Nat))
		(<= (value_int (l11 it) alength) (value_int (l11 it) i))
	)
)

(conjecture
	(forall ((j Int))
		(=>
			(and
				(<= 0 (value_const_int blength))
				(<= 0 j)
				(< j (value_int main_end alength))
			)
			(= (select (value_arr main_end a) j) (select (value_const_arr b) j))
		)
	)
)