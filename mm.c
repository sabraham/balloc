/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <stdbool.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Tumblebolt",
    /* First member's full name */
    "Sunil Abraham",
    /* First member's email address */
    "s.abraham@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


typedef struct block {
  size_t size;
  struct block *l, *r;
} __attribute__((aligned(16))) Block;

Block *free_heap;
size_t heap_size;

/*******************************************************************************
 * Block manipulation functions
 ******************************************************************************/

Block *next_block(Block *b) {
  Block *ret = (Block *) (((char *) b) + b->size + sizeof(Block));
  return ret;
}

/*******************************************************************************
 * Helper debugging / print functions
 ******************************************************************************/

void print_node (Block *node) {
  printf("%p-%p %u\n", node, ((char *) node) + node->size + sizeof(Block),
         (unsigned int) node->size);
}

void print_tree (Block *head) {
  if (!head)
    return;
  print_tree(head->l);
  print_node(head);
  print_tree(head->r);
}

Block *priv_malloc (size_t size) {
  assert(ALIGN(size) == size);
  Block *ret = mem_sbrk(size + sizeof(Block));
  if ((intptr_t) ret == -1) {
    return 0;
  } else {
    heap_size += size;
    ret->size = size;
    ret->l = 0;
    ret->r = 0;
    return ret;
  }
}

/*******************************************************************************
 * Free tree functions
 * \_initializing
 ******************************************************************************/

void init_free_tree () {
  heap_size = 0;
  free_heap = priv_malloc(ALIGNMENT);
  free_heap->size = heap_size;
  free_heap->l = 0;  free_heap->r = 0;
}

bool is_adj (Block *p, Block *q) {
  if (q < p)
    return is_adj(q, p);
  return next_block(p) == q;
}


/*******************************************************************************
 * Free tree functions
 * \_searching
 ******************************************************************************/

Block **find_free_tree (Block **head, Block *child) {
  Block **p = head;
  while (*p && *p != child) {
    if (child < *p) {
      p = &((*p)->l);
    } else if (child > *p){
      p = &((*p)->r);
    } else {
      p = p;
    }
  }
  return p;
}

Block **find_parent_free_tree (Block **head, Block *child) {
  Block **p = head, **q = NULL;
  if (*p && *p != child) q = p;
  while (*p && *p != child) {
    q = p;
    if (child < *p) {
      p = &((*p)->l);
    } else {
      p = &((*p)->r);
    }
  }
  return q;
}

Block *find_min_free_tree(Block **head) {
  Block **ret = head;
  while ((*ret)->l)
    *ret = (*ret)->l;
  return *ret;
}

Block *find_max_free_tree(Block **head) {
  Block **ret = head;
  while ((*ret)->r)
    *ret = (*ret)->r;
  return *ret;
}

Block *find_successor_free_tree (Block **head, Block *node) {
  if (!node) return NULL;
  Block **succ, *next;
  for (next = next_block(node); !(succ = find_free_tree(head, next));
       next = next_block(next)) {}
  return *succ;
}

Block *find_predecessor_free_tree (Block **head, Block *node) {
  if (!node) return NULL;
  if (node->l)
    return find_max_free_tree(&node->l);
  Block **par = find_parent_free_tree(head, node);
  if (!par)
    return NULL;
  Block *p = node;
  while (*par && p == (*par)->l) {
    p = *par;
    par = find_parent_free_tree(head, *par);
    if (!par)
      return NULL;
  }
  return *par;
}

/*******************************************************************************
 * Free tree functions
 * \_removing node
 ******************************************************************************/

void remove_free_tree (Block **head, Block *child) {
  Block **p = find_free_tree(head, child);
  Block *p_child;
  // if child has two children
  if ((*p)->l && (*p)->r) {
    Block **q = &(*p)->l;
    while ((*q)->r)
      q = &(*q)->r;
    Block *q1 = find_predecessor_free_tree(head, *p);
    if (q1 != *q) {
      __asm__("int3\n");
    }
    // check if we didn't move right
    if (*q == (*p)->l) {
      Block *old_r = (*p)->r;
      *p = *q;
      (*p)->r = old_r;
      assert(*p != (*p)->l);
      assert(*p != (*p)->r);
    } else {
      Block *old_l = (*p)->l;
      Block *old_r = (*p)->r;
      Block *old_q = *q;
      remove_free_tree(&old_l, *q);
      *p = old_q;
      (*p)->l = old_l;
      (*p)->r = old_r;
      assert(*p != (*p)->l);
      assert(*p != (*p)->r);
    }
  } // if child has one child
  else if ((p_child = ((*p)->l ? (*p)->l : (*p)->r)) != 0) {
    *p = p_child;
  } else {
    *p = 0;
  }
  child->l = 0;
  child->r = 0;
}

/*******************************************************************************
 * Free tree functions
 * \_removing node
 ******************************************************************************/

void coalesce (Block *p, Block *q) {
  p->size += q->size + sizeof(Block);
  remove_free_tree(&free_heap, q);
}

/*******************************************************************************
 * Free tree functions
 * \_inserting node
 ******************************************************************************/

Block *insert_free_tree (Block **head, Block *child) {
  // insert child into tree with root head child should not already be
  // in  the tree. if it is, malloc's behavior is undefined. in this
  // implementation, we return a null pointer
  Block **p = find_free_tree(head, child);
  *p = child;
  Block *pred = find_predecessor_free_tree(head, child);
  if (pred && is_adj(pred, child)) {
    coalesce(pred, child);
    child = pred;
  }
  // Coalesing successor is broken b.c. find_successor takes very long
  // time to terminate
  Block *succ = find_successor_free_tree(head, child);
  if (succ && is_adj(child, succ)) {
    coalesce(child, succ);
  }
  return child;
}

/*******************************************************************************
 * Free tree functions
 * \_inserting node
 ******************************************************************************/

Block *fit (Block *head, size_t size) {
  Block *ret;
  if (!head) return NULL;
  if((ret = fit(head->l, size)))
    ;
  else if (head->size >= size)
    ret = head;
  else
    ret = fit(head->r, size);
  return ret;
}

/*******************************************************************************
 * Public facing allocating functions
 ******************************************************************************/

int mm_init(void) {
  init_free_tree();
  return 0;
}

void *mm_malloc(size_t size) {
  size = ALIGN(size);
  Block *p = fit(free_heap, size);
  if (!p) {
    p = priv_malloc(size);
    p = insert_free_tree(&free_heap, p);
  }
  if (size == p->size || (p->size - size < sizeof(Block) + ALIGNMENT)) {
    remove_free_tree(&free_heap, p);
  } else {
    Block *q = (Block *) ((char *) p + (p->size - size));
    q->size = size;
    q->l = 0;
    q->r = 0;
    p->size -= size + sizeof(Block);
    p = q;
  }
  return (void *) (p + 1);
}

void mm_free(void *ptr) {
  Block *p = ((Block *) ptr) - 1;
  insert_free_tree(&free_heap, p);
}

void *mm_realloc(void *p, size_t new_size)
{
  void *ret;
  size_t old_size = (((Block *) p) - 1)->size;
  ret = mm_malloc(new_size);
  memcpy(ret, p, old_size < new_size ? old_size : new_size);
  mm_free(p);
  return ret;
}
