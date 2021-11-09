// If there is at least one iteration and therefore there is a last iteration, then in that last iteration, j is set to 1.
// Therefore it's 1 at the end of the loop.
// Seems to be difficult since we need to use the iteration before the last one.
// Update: should be solved by at-least-one-iteration lemma

func main()
{
	const Int[] a;
	const Int alength;

	Int i = 0;
	Int j = 0;
	while(i < alength)
	{
		i = i + 1;
		j = 1;
	}
}

(axiom
  (<= 0 alength)
)

(conjecture
	(=>
		(< 0 alength)
		(= (j main_end) 1)
	)
)
