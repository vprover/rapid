struct Node {
  Int data;
  Node* next;
};

func main() {
  const Int len;
  Int flag;

  Node* a = malloc();
  a->next = NULL;
  Node* p = a;
  Node* t;

  Int counter = 0;
  while(counter < len) {
    if(flag > 0){
      p->data = 1;
    } else {
      p->data = 2;
    }
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    counter = counter + 1;
  }
  p->data = 3;

  p = a;
  if(flag > 0){
    while(p->data == 1) {
      p = p->next;
    }
  } else {
    while(p->data == 2) {
      p = p->next;
    }  
  }
}

(axiom
  (<= 10 (value_const len))
)

(conjecture
  (= 
    (node_data main_end (value_node main_end p)) 
    3
  )
)

