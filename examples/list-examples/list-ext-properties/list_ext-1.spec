struct Node {
  Int data;
  Node* next;
};

func main() {
  const Int len1;
  const Int len2;

  Node* a = malloc();
  a->next = NULL;
  Node* p = a;
  Node* t;

  Int i = 0;
  while(i < len1) {
    p->data = 1;
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    i = i + 1;
  }


  Int y = 0;
  while(y < len2) {
    p->data = 2;
    t = malloc();
    t->next = NULL;
    p->next = t;
    p = p->next;
    y = y + 1;
  }

  p->data = 3;
  p->next = NULL;

  p = a;
  while(p->data == 1){
    p = p->next;
  }
  while(p->data == 2){
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

