func main() {
	const Int[] a;
	const Int alength;
	const Int x;

	Int i = 0;

	while (i < alength) {
		if (a[i] == x) {
			return i;
		}
		i = i + 1;
	}
}

(conjecture
	(=>
		(<= 0 alength)
		(or
			(= x (a main_end (i main_end)))
			(<= alength (i main_end))
		)
	)
)
