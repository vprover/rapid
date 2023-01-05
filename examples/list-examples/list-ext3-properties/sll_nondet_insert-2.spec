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

  const Int k;
  i = 0;
  while(i < k){
    Int position;
    Node* new_node = malloc();
    
    Node* second_to_last = NULL;
    Node* last = head;
    while(position > 0){
      second_to_last = last;
      last = last->next;
      position = position - 1;
    }
    new_node->next = last;
    if(second_to_last != NULL){
      second_to_last->next = new_node;
    } else {
      head = new_node;
    }

    i = i + 1;
  }

  Int count = 0;
  while(head != NULL) {
    head = head->next;
    count = count + 1;
  }

}

(axiom
  (< 0 (value_const len))
)

(axiom
  (and
    (<= 0 (value_const k))
    (< (value_const k) (value_const len))
  )
)

(axiom
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (< it nl20)
      )
      (and
        (<= 0 (value (l22 it) position))
        (< (value (l22 it) position) 
           (+ (value (l20 it) i) (value_const len) )
        )
      )
    )
  )
)

(conjecture
  (= (value main_end count) 
     (+ (value_const len) (value_const k)) 
  )
)