struct Node {
  Int data;
  Node* next;
};

func main() {
  const Int len;

  Node* a = malloc();
  a->next = NULL;
  Node* p = a;
  Node* t;

  Int counter = 0;
  while(counter < len) {
    p->data = counter;
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    counter = counter + 1;
  }

  p->data = counter;
  p->next = NULL;
  p = a;

  while(p != NULL) {
    p = p->next;
  }

}

(axiom
  (<= 10 (value_const len))
)

(conjecture
   (exists ((it Int)) 
      (= (node_data (l28 it) (value_node (l28 it) p)) 2)
   )
)

