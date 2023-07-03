struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  const Int len;
  const Int dat = 1;

  Int i = len;
  while(i > 0) {
    Node* node = malloc();
    node->next = NULL;
    node->data = dat;
    node->next = head;
    head = node;
    i = i - 1;
  }


  const Int unequal = 5;
  Node* node2 = malloc();
  node2->next = NULL;
  node2->data = unequal;

  if(head == NULL){
    head = node2;
  } else {
    Node* last = head;
    while(last->next != NULL){
      last = last->next;
    }
    last->next = node2;
  }

  Int counter = 0;
  while(head->next != NULL) {
    head = head->next;
    counter = counter + 1;
  }
  counter = counter + 1;

}


(axiom
  (<= 0 (value_const len))
)

(conjecture
  (= (value main_end counter) (+ (value_const len) 1))
)

