struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  const Int len;
  const Int index;
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

  const Int new_dat = 5;
  Node* node2 = malloc();
  node2->next = NULL;
  node2->data = new_dat;

  Node* last = head;
  Node* snd_to_last = NULL;

  Int idx = index;
  while(idx > 0){
    snd_to_last = last;
    last = last->next;
    idx = idx - 1;
  }
  if(snd_to_last != NULL){
    snd_to_last->next = node2;
  } else {
    head = node2;
  }
  node2->next = last;

  while(head != NULL && idx != index){
    head = head->next;
    idx = idx + 1;
  }

  head = head->next;
  idx = idx + 1;

  while(head != NULL){
    head = head->next;
    idx = idx + 1;
  }

}


(axiom
  (<= 10 (value_const len))
)

(axiom
  (= 
    (value_const len)
    (* 2 (value_const index))
  )
)

(axiom
  (< 0 (value_const index))
)

(conjecture
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (< it nl43)
      )
      (= (node_data (l43 it) (value_node (l43 it) head)) 1)
    )
  )
)
