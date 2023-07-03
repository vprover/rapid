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

  const Int new_dat = 5;
  Node* node2 = malloc();
  node2->next = head;
  node2->prev = NULL;
  node2->data = new_dat;

  if(head != NULL){
    head->prev = node2;
  } else {
    skip;
  }
  head = node2;

  head = head->next;
  Int count = 1;
  while(head != NULL) {
    head = head->next;
    count = count + 1;
  }

}

(axiom
  (<= 0 (value_const len))
)

(conjecture
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (< it nl43)
      )
      (= (node_data (l43 it) (value_node (l43 it) head)) 1)
    )
  )
)

