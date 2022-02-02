func main() {
	const Int[] a;
	const Int alength;
	Int sum = 0;
	Int i = 0;
	while (i < alength) {
		if (a[i] < 0) {
			continue;
		}
		i = i + 1;
		sum = sum + a[i];
	}
}

(conjecture
	(<= 0 (sum main_end))
)
