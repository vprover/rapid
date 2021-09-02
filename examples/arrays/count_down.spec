func main()
{
	Int x;

	x = x * x;

	while (x > 2)
	{
      x = x - 1;
	}
}

(axiom
  (> (x l5) 2)
)

(conjecture
	(= (x main_end) 2)
)