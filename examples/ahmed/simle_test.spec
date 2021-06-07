func main() {
  Int c;
  c = 5;
  Int* d = &c;
  Int[] a;
  Int[] b;
  b[10] = 3;
  a[2] = 10;
  a[5] = 7;
  Int temp = a[2];
  a[2] = a[5];
  a[5] = temp;
}

(conjecture
  (and 
    (= (a main_end 2) 7)  
    (= (a main_end 5) 10)
    (= (b main_end 10) 3)
  )
)