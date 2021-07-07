// example which shows that we need the requirement that array-lengths are nonnegative: 
// If we remove the precondition "0 <= (value_const_int alength)", then neither the standard-encoding nor 
// the timepoint encoding is able to prove the postcondition "i == (value_const_int alength)".
// In particular, the following property is not valid:
// (conjecture
// 		 (= (value_int main_end i) (value_const_int alength))
// )

func main()
{
	const Int alength;
	Int i = 0;

	while (i < alength)
	{
		i = i + 1;
	}
}

(conjecture
	(not 
		(< (value_int main_end i) (value_const_int alength))
	)
)

(conjecture
	(=>
		(<= 0 (value_const_int alength))
		(= (value_int main_end i) (value_const_int alength))
	)
)
