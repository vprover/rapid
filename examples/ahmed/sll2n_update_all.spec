struct Node {
  Int data;
  Node* next;
};

func main() {
  Int len = 20;
  Int dat = 1;

  Int i = len;
  Node* head = NULL;
  while(i > 0) {
    Node* node = malloc();
    node->next = NULL;
    node->data = dat;
    node->next = head;
    head = node;
    i = i - 1;
  }
  
  Int j = 0;
  while(j < len) {
    Int new_data = j + len;
    Int k = 0;
    Node* curr = head;
    while(k < j){
      curr = curr->next;
      k = k + 1;
    }
    curr->data = new_data;
    j = j + 1; 
  }

}

(conjecture
  (= (deref main_end head) null_loc)
)