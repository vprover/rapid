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

  i = len;
  while(i > 0) {
    if(head->next == NULL){
      head = NULL;
    } else {
      Node* snd_to_last = NULL;
      Node* last = head;
      while(last->next != NULL){
        snd_to_last = last;
        last = last->next;
      }
      snd_to_last->next = NULL;
    }
    i = i - 1;
  }

}


(axiom
  (<= 0 (value_const len))
)

(conjecture
  (= (value_node main_end head) node_null_loc)
)

