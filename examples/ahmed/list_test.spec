struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  Node* n = malloc();
  n->next = head;
  n->data = 20;
}

(conjecture
  (= (deref main_end head) null_loc)
)