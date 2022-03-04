struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  Int len = 20;
  Int dat = 1;

  Int i = len;
  while(i > 0) {
    Node* node = malloc();
    node->next = NULL;
    node->data = dat;
    node->next = head;
    head = node;
    i = i - 1;
  }

}

(conjecture
  (= (value main_end head) null_loc)
)