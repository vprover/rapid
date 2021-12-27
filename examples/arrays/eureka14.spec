func main() {
  Int i;
  Int[] a;
  const Int alength;
    
  a[20] = 0;
  i = 0;
  while((a[i]!=0) && (i<alength)){
    a[i] = 2*i;
    i = i+1;
  }
}

(axiom
  (> alength 20)
)

(conjecture
  (< (i main_end) alength)
)