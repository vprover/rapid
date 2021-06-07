func main() {
  Int[] pointers;
  Int[] values;
  Int temp;

  temp = values[pointers[0]];

  values[pointers[0]] = values[pointers[1]];
  values[pointers[1]] = temp;
}

(conjecture
  (and 
    (= (values main_end (pointers main_end 0)) (values l6 (pointers l6 1)))  
    (= (values main_end (pointers main_end 1)) (values l6 (pointers l6 0)))  
  )
)