/* ukkonen.c
 * suffix tree construction algorithm
 */

/* NULL pointer definition */
#define NULL ((void*)0)

/* maximum number of nodes to be used */
unsigned int max_nodes_nb;
/* size of the alphabet we work with */
unsigned int alphabet_sz;
/* maximum size of the processed string */
unsigned int max_string_sz;

/* node structure */
typedef struct struct_node
{
  unsigned int exit;
  struct struct_node **sons;
} node;

/* list of all available nodes */
node *nodes_list;

/* index of the next free node */
unsigned int next_node;

/* nodes list related invariants, predicates and axioms
 ******************************************************
 */

/*@ predicate valid_node(node *p)
  @ { \exists int k; (0 <= k < max_nodes_nb) && p == nodes_list + k }
  @*/

/*@ predicate valid_sons(node *p)
  @ { \forall int k; 0 <= k < alphabet_sz
  @     => (p->sons[k] == \null || valid_node(p->sons[k])) }
  @*/

/*@ invariant valid_nodes_range: \valid_range(nodes_list,0,max_nodes_nb-1) */

/*@ invariant valid_sons_range: \forall node *t; valid_node(t)
  @   => \valid_range(t->sons,0,alphabet_sz-1)
  @*/

/*@ invariant valid_sons_links:
  @   \forall node *t; valid_node(t) => valid_sons(t)
  @*/

/*@ invariant node_validity:
  @   \forall node *t; valid_node(t) => \valid(t)
  @*/

/* source word and related invariants
 ************************************
 */

/* word we are working on */
unsigned int *current_word;

/*@ invariant valid_word_range: \valid_range(current_word,0,max_string_sz-1) */
/*@ invariant valid_word_chars:
  @   \forall int k; 0 <= k < max_string_sz
  @     => (0 <= current_word[k] < alphabet_sz)
  @*/
/*@ invariant valid_word_end:
  @   \exists int n; 0 <= n < max_string_sz && current_word[n] == 0
  @*/
/*@ invariant end_mark_in_limit:
  @   \forall int n; (0 <= n < max_string_sz && current_word[n] != 0)
  @     => 0 <= n < max_string_sz - 1
  @*/

/* WARNING:
 * max_nodes_nb, alphabet_sz, nodes_list, next_node,
 * max_string_sz, and current_word must be initialized
 * before any call to the construction function (we don't
 * care about memory allocation or initialization here).
 */

/* suffix tree related invariants, predicates and axioms
 *******************************************************
 */

/*@ invariant nodes_nb_floor:
  @   1 < max_string_sz * max_string_sz < max_nodes_nb - 1
  @*/

/* word's character retrieving function */
/****************************************/
/*@ requires
  @   0 <= i < max_string_sz
  @ ensures
  @   0 <= \result < alphabet_sz &&
  @   \result == current_word[i]
  @*/
unsigned int get_char(unsigned int i)
{ return current_word[i]; }

/* fresh node allocation function */
/**********************************/
/*@ requires
  @   0 <= next_node < max_nodes_nb - 1
  @ assigns next_node
  @ ensures
  @   \result == nodes_list + \old(next_node) &&
  @   next_node == \old(next_node) + 1
  @*/
node *get_fresh_node()
{
  node *n = &(nodes_list[next_node]);
  /* note that we don't need to check wether n is NULL or */
  /* not since it is *not*, as required in pre-condition  */
  next_node++;
  return n;
}

/* target research function */
/****************************/
/*@ requires
  @   0 <= c < alphabet_sz && valid_node(t)
  @ ensures
  @   \result != \null => valid_node(\result)
  @*/
node *target(node *t, unsigned int c)
{ return t->sons[c]; }

/* suffix head research function */
/*********************************/
/*@ requires
  @   valid_node(m) && \valid(r) &&
  @   0 <= i < max_string_sz &&
  @   \base_addr(r) != \base_addr(current_word)
  @ assigns *r
  @ ensures
  @   0 <= *r < max_string_sz && valid_node(\result)
  @*/
node *locate_head(node *m, unsigned int i, unsigned int *r)
{
  /*@ invariant 0 <= i < max_string_sz && valid_node(m)
    @ variant max_string_sz - i
    @*/
  while(i < (max_string_sz - 1))
  {
    node *t = target(m,get_char(i));
    if(t == NULL) break;
    m = t;
    i++;
  }
  *r = i;
  return m;
}

/* node's son insertion function */
/*********************************/
/*@ requires
  @   valid_node(f) && valid_node(s) &&
  @   0 <= i < max_string_sz
  @ assigns f->sons[..]
  @ ensures valid_node(f)
  @*/
void insert_son(node *f, node *s, unsigned int i)
{/*@ assert 0 */ f->sons[get_char(i)] = s; }

/* suffix tree construction function */
/*************************************/

/*@ predicate loops_invariant() 
  @ {
  @   \valid_range(nodes_list,0,max_nodes_nb-1) &&
  @   \valid_range(current_word,0,max_string_sz-1) &&
  @   (\forall int k; (0 <= k < max_string_sz) =>
  @     (0 <= current_word[k] < alphabet_sz)) &&
  @   (\forall node *t; valid_node(t) => valid_sons(t)) &&
  @   (\forall node *t; valid_node(t) =>
  @     \valid_range(t->sons,0,alphabet_sz-1))
  @ }
  @*/

/*@ requires
  @   0 < max_string_sz &&
  @   next_node == 0 &&
  @   max_nodes_nb > 1
  @ ensures
  @   valid_node(\result)
  @*/
node *build_suffix_tree()
{
  node *m = get_fresh_node();
  unsigned int i;
  unsigned int k;
  /*@ assert 0 */
  /*@ invariant
    @   0 <= next_node <= 2 + i * max_string_sz &&
    @   0 <= i < max_string_sz && loops_invariant()
    @ loop_assigns nodes_list[..].sons[..],nodes_list[..].exit,next_node,i
    @ variant max_string_sz - i
    @*/
  for(i = 0; get_char(i) != 0; i++)
  {
    node *p = locate_head(m,i,&k);
    unsigned int j;
    /*@ label suffix_add_beginning */
    /*@ invariant
      @   next_node - \at(next_node,suffix_add_beginning) == j - k &&
      @   k <= j < max_string_sz - 2 && valid_node(p) && loops_invariant()
      @ loop_assigns nodes_list[..].sons[..],next_node,j
      @ variant max_string_sz - j
      @*/
    for(j = k; get_char(j) != 0; j++)
    {
      node *q = get_fresh_node();
      insert_son(p,q,j);
      p = q;
    }
    p->exit = i;
  }
  m->exit = i;
  return m;
}

