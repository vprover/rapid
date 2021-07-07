// find the maximal element in the array
// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_27_true-unreach-call_ground.c

func main()
{
	const Int[] a;
	const Int alength;

	Int i = 1;
	Int max = a[0];
	while (i < alength)
	{
		if (a[i] > max)
		{
			max = a[i];
		}
		else
		{
			skip;
		}
		i = i + 1;
	}
}

(conjecture
	(forall ((k Int))
		(=>
			(and
				(<= 0 (value_const_int alength))
				(<= 0 k)
				(< k (value_const_int alength))
			)
			(<= (select (value_const_arr a) k) (value_int main_end max))
		)
	)
)

(conjecture
	(=>
		(<= 0 (value_const_int alength))
		(exists ((k Int))
			(and
				(<= 0 k)
				(< k (value_const_int alength))
				(= (select (value_const_arr a) k) (value_int main_end max))
			)
		)
	)
)
