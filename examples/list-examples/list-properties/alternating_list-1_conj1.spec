struct Node {
  Int data;
  Node* next;
};

func main() {
  const Int len;
  Int flag = 1;

  Node* a = malloc();
  a->next = NULL;
  Node* p = a;
  Node* t;

  Int counter = 0;
  while(counter < len) {
    if(flag == 1){
      p->data = 1;
      flag = 0;
    } else {
      p->data = 2;
      flag = 1;
    }
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    counter = counter + 1;
  }

  p->data = 3;
  p->next = NULL;
  p = a;
  flag = 1;

  while(p->data != 3) {
    if(flag == 1){
      flag = 0;
    } else {
      flag = 1;
    }
    p = p->next;
  }
}

(axiom
  (<= 10 (value_const len))
)

(conjecture
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (< it nl36)
      )
      (= 
        (node_data (l38 it) (value_node (l38 it) p)) 
        1
      )
    ) 
  )
)

