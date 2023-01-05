extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern int __VERIFIER_nondet_int();

/*
 * Create NULL-terminated sll of size 2: 1-1
 * Append node with data = 5. Check result: 1-1-5
 */
#include <stdlib.h>

typedef struct node {
  int data;
  struct node* next;
} *SLL;

void myexit(int s) {
 _EXIT: goto _EXIT;
}

int _get_nondet_int(int larger_than) {
  int res = __VERIFIER_nondet_int();
  while(res <= larger_than) {
    res = __VERIFIER_nondet_int();
  }
  return res;
}

SLL node_create(int data) {
  SLL temp = (SLL) malloc(sizeof(struct node));
  if(NULL == temp) {
    myexit(1);
  }
  temp->next = NULL;
  temp->data = data;
  return temp;
}

SLL sll_create(int len, int data) {
  SLL head = NULL;
  for(; len > 0; len--) {
    SLL new_head = node_create(data);
    new_head->next = head;
    head = new_head;
  }
  return head;
}

void sll_destroy(SLL head) {
  while(head) {
    SLL temp = head->next;
    free(head);
    head = temp;
  }
}

void sll_append(SLL* head, int data) {
  SLL new_last = node_create(data);
  if(NULL == *head) {
    *head = new_last;
  } else {
    SLL last = *head;
    while(last->next) {
      last = last->next;
    }
    last->next = new_last;
  }
}

int main() {

  const int len = _get_nondet_int(10);
  const int data = 1;
  SLL s = sll_create(len, data);

  const int uneq = 5;
  sll_append(&s, uneq);

  SLL ptr = s;
  int count = 0;
  if(ptr->next) {
    while(ptr->next) {
      SLL temp = ptr->next;
      if(data != ptr->data) {
  goto ERROR;
      }
      ptr = temp;
      count++;
    }
    count++;
  }

  sll_destroy(s);

  return 0;
 ERROR: {reach_error();abort();}
  return 1;
}
