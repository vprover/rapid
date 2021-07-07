func main()
{
	const Int[] a;
	Int i = 0;
	while(a[i] != 0)
	{
		i = i + 1;
	}
}

(conjecture
	(=>
		(exists ((pos Int))
			(and
				(<= 0 pos)
				(= (select (value_const_arr a) pos) 0)
			)
		)
		(forall ((j Int))
			(=>
				(and
					(<= 0 j)
					(< j (value_int main_end i))
				)
				(not (= (select (value_const_arr a) j) 0 ))
			)
		)
	)
)
