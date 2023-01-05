struct Node {
  Node* next;
};

func main() {
  Node* head = NULL;
  const Int len;

  Int i = len;
  while(i > 0) {
    Node* node = malloc();
    node->next = NULL;
    node->next = head;
    head = node;
    i = i - 1;
  }

  Int count = 0;
  while(head != NULL) {
    head = head->next;
    count = count + 1;
  }

}

(axiom
  (<= 2 (value_const len))
)

(conjecture
  (= (value main_end count) (value_const len))
)