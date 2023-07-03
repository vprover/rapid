struct Node {
  Int data;
  Node* next;
  Node* prev;
};

func main() {
  Node* head = NULL;
  const Int len;
  const Int dat = 1;

  Int i = len;
  while(i > 0) {
    Node* node = malloc();
    node->next = NULL;
    node->prev = NULL;
    node->data = dat;
    node->next = head;
    if(head != NULL){
      head->prev = node;
    } else {
      skip;
    }
    head = node;
    i = i - 1;
  }

  Node* node2 = malloc();
  node2->next = head;
  node2->prev = NULL;
  node2->data = dat;
  if(head != NULL){
    head->prev = node2;
  } else {
    skip;
  }
  head = node2;

  Int count = 0;
  while(head != NULL) {
    head = head->next;
    count = count + 1;
  }

}


(axiom
  (<= 0 (value_const len))
)

(conjecture
  (= (value main_end count) (+ (value_const len) 1))
)