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
          (< it nl35)
        )
        (= 
          (node_data (l42 it) (value_node (l42 it) temp2)) 
          (+ (value (l42 it) i) (value_const len))
        )
      ) 
   )
)