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

  Int j = len;
  while(j > 0) {
    head = head->next;
    j = j - 1;
  }

}

(axiom
  (<= 0 (value_const len))
)

(conjecture
  (= (value_node main_end head) node_null_loc)
)