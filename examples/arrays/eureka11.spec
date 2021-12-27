func main(){
  Int[] a;
  Int j = 0;

  a[0]=0;
  a[99999]=3;

  while(j<50000){
    a[j]=a[99999-j];
    j=j+1;
  }
}

(conjecture
  (not
    (= (a main_end 0) 0)
  )
)