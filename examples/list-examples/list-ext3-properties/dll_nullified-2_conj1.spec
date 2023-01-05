struct Node {
  Int data_0;
  Node* next;
  Int data_1;
  Node* prev;
  Int data_2;
};

func main() {
  Node* head = NULL;
  const Int len;

  Int i = len;
  while(i > 0) {
    Node* node = malloc();

    node->data_0 = 0;
    node->data_1 = 0;
    node->data_2 = 0;

    node->next = head;
    node->prev = NULL;

    if(head != NULL){
      head->prev = node;
    } else {
      skip;
    }
    head = node;
    i = i - 1;
  }

  while(head->next != NULL) {
    head = head->next;
  }

  while(head != NULL) {
    head = head->prev;  
  }
}

(axiom
  (<= 10 (value_const len))
)

(conjecture
  (forall ((it Int))
    (=>
      (and
        (<= 0 it)
        (<= it nl33)
      )
      (and
        (= (node_data_0 (l33 it) (value_node (l33 it) head)) 0)
        (= (node_data_1 (l33 it) (value_node (l33 it) head)) 0)
        (= (node_data_2 (l33 it) (value_node (l33 it) head)) 0)
      )
    )
  )
)