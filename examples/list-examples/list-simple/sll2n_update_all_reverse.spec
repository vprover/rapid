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


  i = len - 1;
  while(i >= 0) {
    Node* temp = head;
    Int j = i;
    while(j > 0){
      temp = temp->next;
      j = j - 1;
    }
    temp->data = i + len;
    i = i - 1;
  }

  i = len - 1;
  while(i >= 0){
    Node* temp2 = head;
    Int j2 = i;
    while(j2 > 0){
      temp2 = temp2->next;
      j2 = j2- 1;
    }
    i = i - 1;  
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

