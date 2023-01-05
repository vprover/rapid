struct Node {
  Int data;
  Node* next;
};

func main() {
  const Int len1;
  const Int len2;
  Int flag = 1;

  Node* a = malloc();
  a->next = NULL;
  Node* p = a;
  Node* t;

  Int counter = 0;
  while(counter < len1) {
    p->data = 1;
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    counter = counter + 1;
  }
  counter = 0;
  while(counter < len2) {
    p->data = 2;
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    counter = counter + 1;
  }  
  p->data = 3;

  p = a;
  while(p->data == 1) {
    p = p->next;
  }
  while(p->data == 2) {
    p = p->next;
  }  
}

(axiom
  (<= 10 (value_const len1))
)

(axiom
  (<= 10 (value_const len2))
)

(conjecture
  (= 
    (node_data main_end (value_node main_end p)) 
    3
  )
)

