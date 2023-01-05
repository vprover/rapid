struct Node {
  Int data;
  Node* next;
};

func main() {
  const Int len;

  Node* p = NULL;
  Int i = len;

  while(i > 0) {
    Node* node = malloc();
    node->next = NULL;
    node->data = 1;
    node->next = p;
    p = node;
    i = i - 1;
  }


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
          (< it nl22)
        )
        (= 
          (node_data (l22 it) (value_node (l22 it) p)) 
          1
        )
      ) 
   )
)

