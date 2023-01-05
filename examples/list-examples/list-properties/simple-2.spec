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
    p->data = 1;
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    counter = counter + 1;
  } 
  p->data = 1;

  p = a;
  while(p != NULL) {
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
          (< it nl26)
        )
        (= 
          (node_data (l26 it) (value_node (l26 it) p)) 
          1
        )
      ) 
   )
)

