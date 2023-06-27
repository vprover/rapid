struct Node {
  Int data;
  Node* next;
  Node* prev;
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

  const Int new_dat = 5;
  Node* node2 = malloc();
  node2->next = NULL;
  node2->prev = NULL;  
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
    node2->prev = snd_to_last;
    node2->next = last;
    if(last != NULL){
      last->prev = node2;
    } else {
      skip;
    }
  } else {
    node2->next = head;
    if(head != NULL){
      head->prev = node2;
    } else {
      skip;
    }
    head = node2;
  }

  Int count = 0;
  while(head != NULL && count != index) {
    head = head->next;
    count = count + 1;
  }

  head = head->next;
  count = count + 1;

  while(head != NULL){
    head = head->next;
    count = count + 1;
  }
}

(axiom
  (<= 10 (value_const len))
)

(axiom
  (= 
    (value_const len)
    (* 2 (value l10 index))
  )
)

(axiom
  (< 0 (value l10 index))
)

(conjecture
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (< it nl72)
      )
      (= (node_data (l72 it) (value_node (l72 it) head)) 1)
    )
  )
)