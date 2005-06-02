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
/*@ invariant valid_nodes: \valid_range(nodes_list,0,max_nodes_nb-1) */
/*@ predicate valid_node(node *p)
  @ { \exists int k; \valid_index(nodes_list,k) && p == nodes_list + k }
  @*/
/*@ invariant valid_sons_range: \forall node *t; valid_node(t)
  @   => \valid_range(t->sons,0,alphabet_sz-1) */
/*@ predicate valid_sons(node *p)
  @ { \forall int k; 0 <= k < alphabet_sz
  @     => (p->sons[k] == \null || valid_node(p->sons[k])) }
  @*/
/*@ axiom node_validity:
  @   \forall node *t; valid_node(t) => \valid(t)
  @*/
/*@ invariant valid_sons_links:
  @   \forall node *t; valid_node(t) => valid_sons(t)
  @*/

/* index of the next free node */
unsigned int next_node;
/*@ invariant next_node_sup: next_node < max_nodes_nb */

/* word we are working on */
unsigned int *current_word;
/*@ invariant valid_word: \valid_range(current_word,0,max_string_sz-1) &&
  @   \forall int k; \valid_index(current_word,k) =>
  @   (0 <= current_word[k] < alphabet_sz)
  @*/

/* WARNING:
 * max_nodes_nb, alphabet_sz, nodes_list, next_node,
 * max_string_sz, and current_word must be initialized
 * before any call to the construction function (we don't
 * care about memory allocation or initialization here).
 */

/* word's character retrieving function */
/*@ requires
  @   \valid_index(current_word,i)
  @ ensures
  @   0 <= \result < alphabet_sz &&
  @   \result == current_word[i]
  @*/
unsigned int get_char(unsigned int i)
{ return current_word[i]; }

/* fresh node allocation function */
/*@ requires next_node < max_nodes_nb - 1
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
/*@ requires 0 <= c < alphabet_sz && valid_node(t)
  @ ensures \result != \null => valid_node(\result)
  @*/
node *target(node *t, unsigned int c)
{ return t->sons[c]; }

/* suffix head research function */
/*@ requires
  @   valid_node(m) && \valid(r) && \valid_index(current_word,i) &&
  @   \base_addr(r) != \base_addr(current_word)
  @ assigns *r
  @ ensures \valid_index(current_word,*r) && valid_node(\result)
  @*/
node *locate_head(node *m, unsigned int i, unsigned int *r)
{
  /*@ invariant \valid_index(current_word,i) && valid_node(m)
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
/*@ requires
  @   valid_node(f) &&
  @   valid_node(s) &&
  @   \valid_index(current_word,i)
  @ assigns f->sons[..]
  @*/
void insert_son(node *f, node *s, unsigned int i)
{ f->sons[get_char(i)] = s; }

/* suffix tree construction function */
/*@ assigns nodes_list,next_node
  @ ensures valid_node(\result)
  @*/
node *build_suffix_tree()
{
  node *m = get_fresh_node();
  unsigned int i;
  if(m == NULL) return NULL;
  /*@ invariant \valid_index(current_word,i)
    @ variant max_string_sz - i
    @*/
  for(i = 0; i < max_string_sz; i++)
  {
    unsigned int k;
    node *p = locate_head(m,i,&k);
    unsigned int j;
    /*@ invariant \valid_index(current_word,j) && valid_node(p)
      @ variant max_string_sz - j
      @*/
    for(j = k; j < max_string_sz; j++)
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

