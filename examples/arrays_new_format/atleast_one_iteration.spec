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

(conjecture
  (=>
    (= 0 (value_const_int alength))
    (= (value_int main_end j) 0)
  )
)

(conjecture
  (=>
    (< 0 (value_const_int alength))
    (= (value_int main_end j) 1)
  )
)
