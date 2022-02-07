struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  Node* n = malloc();
  n->next = head;
  n->data = 20;
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
  
  Int j = len;
  while(j > 0) {
    Node* temp = head->next;
    head = temp;
    j = j - 1; 
  }

}

(conjecture
  (= (deref main_end head) null_loc)
)