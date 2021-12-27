func main(){
  Int[] a;
  Int i = 0;
  Int j = 0;
  
  while(i<100){
    a[i]=0;
    i=i+1;
  }

  while(j<100){
    a[j]=j+1;
    j=j+1;
  }
}

(conjecture
  (not (= (a main_end 1) 0))
)