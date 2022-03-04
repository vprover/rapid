struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  Int len = 20;
  Int dat = 1;

  Node* node = malloc();
  node->next = NULL;
  node->data = dat;
  node->next = head;
  head = node;

  node = malloc();
  node->next = NULL;
  node->data = dat;
  node->next = head;
  head = node;
}

(conjecture
  (= (value main_end head) null_loc)
)