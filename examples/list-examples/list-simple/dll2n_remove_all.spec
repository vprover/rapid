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

  i = 0;
  while(i < len){
    Node* temp = head->next;
    if(temp != NULL){
      temp->prev = NULL;
    } else {
      skip;
    }
    head = temp;
    i = i + 1;
  }
}

(axiom
  (<= 0 (value_const len))
)

(conjecture
  (= (value_node main_end head) node_null_loc)
)

