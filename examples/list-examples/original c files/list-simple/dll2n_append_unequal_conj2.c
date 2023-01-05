extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }
extern int __VERIFIER_nondet_int();

/*
 * Create NULL-terminated dll of size 2: 1-1
 * Append node with data = 5. Check result: 1-1-5
 */
#include <stdlib.h>

typedef struct node {
  int data;
  struct node* next;
  struct node* prev;
} *DLL;

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

DLL node_create(int data) {
  DLL temp = (DLL) malloc(sizeof(struct node));
  if(NULL == temp) {
    myexit(1);
  }
  temp->next = NULL;
  temp->prev = NULL;
  temp->data = data;
  return temp;
}

DLL dll_create(int len, int data) {
  DLL head = NULL;
  while(len > 0) {
    DLL new_head = node_create(data);
    new_head->data = data;
    new_head->next = head;
    if(head) {
      head->prev = new_head;
    }
    head = new_head;
    len--;
  }
  return head;
}

void dll_destroy(DLL head) {
  while(head) {
    DLL temp = head->next;
    free(head);
    head = temp;
  }
}

void dll_append(DLL* head, int data) {
  DLL new_last = node_create(data);
  if(NULL == *head) {
    *head = new_last;
  } else {
    DLL last = *head;
    while(last->next) {
      last = last->next;
    }
    last->next = new_last;
    new_last->prev = last;
  }
}

int main() {

  const int len = _get_nondet_int(10);
  const int data = 1;
  DLL s = dll_create(len, data);

  const int uneq = 5;
  dll_append(&s, uneq);

  DLL ptr = s;
  int count = 0;
  if(ptr->next) {
    while(ptr->next) {
      ptr = ptr->next;
      count++;
    }
    if(uneq != ptr->data) {
      goto ERROR;
    }
    count++;
  }

  dll_destroy(s);

  return 0;
 ERROR: {reach_error();abort();}
  return 1;
}
