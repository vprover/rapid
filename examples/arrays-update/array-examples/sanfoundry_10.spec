// from https://github.com/sosy-lab/sv-benchmarks/blob/master/c/array-examples/sanfoundry_10_ground.c


func main(){
    Int pos;
    const Int element;
    Int found = 0;
    Int[] vector;
    const Int vectorlength;

    Int i = 0;
    while (i < vectorlength && found != 1){
        if (vector[i] == element){
            found = 1;
            pos = i;
        } else {
          skip;
        }
        i = i + 1;
    }
    if (found == 1) {
        i = pos;
        while (i < vectorlength - 1)
        {
            vector[i] = vector[i + 1];
            i = i + 1; 
        }
    } else {
      skip;
    }
}

(conjecture
  (forall ((x Int))
    (=>
      (and
        (<= 0 vectorlength)
        (<= 0 x)
        (< x (- vectorlength 1))
        (= (found main_end) 1)
      )
      (not (= (vector main_end x) element))
    )
  )
)
