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
  node2->next = NULL;
  node2->prev = NULL;  
  node2->data = dat;

  if(head == NULL){
    head = node2;
  } else {
    Node* last = head;
    while(last->next != NULL){
      last = last->next;
    }
    last->next = node2;
    node2->prev = last;
  }

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
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (< it nl45)
      )
      (= (node_data (l45 it) (value_node (l45 it) head)) 1)
    )
  )
)

