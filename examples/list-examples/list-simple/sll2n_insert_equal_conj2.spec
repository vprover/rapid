struct Node {
  Int data;
  Node* next;
};

func main() {
  Node* head = NULL;
  const Int len;
  Int index;
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

  Node* node2 = malloc();
  node2->next = NULL;
  node2->data = dat;

  Node* last = head;
  Node* snd_to_last = NULL;

  while(index > 0){
    snd_to_last = last;
    last = last->next;
    index = index - 1;
  }
  if(snd_to_last != NULL){
    snd_to_last->next = node2;
  } else {
    head = node2;
  }
  node2->next = last;

  Int count = 0;
  while(head != NULL) {
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
  (= (value main_end count) (+ (value_const len) 1))
)

