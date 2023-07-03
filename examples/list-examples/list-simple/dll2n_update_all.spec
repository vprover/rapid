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

  i = 0;
  while(i < len){
    Node* temp2 = head;
    Int j2 = i;
    while(j2 > 0){
      temp2 = temp2->next;
      j2 = j2- 1;
    }
    i = i + 1;  
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
          (< it nl42)
        )
        (= 
          (node_data (l49 it) (value_node (l49 it) temp2)) 
          (+ (value (l49 it) i) (value_const len))
        )
      ) 
   )
)

