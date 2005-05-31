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
/*@ invariant valid_sons: \forall int k; \valid_index(nodes_list,k)
  @   => \valid_range(nodes_list[k].sons,0,alphabet_sz-1)
  */

/* index of the next free node */
unsigned int next_node;
/*@ invariant next_node_sup: next_node < max_nodes_nb */

/* word we are working on */
unsigned int *current_word;
/*@ invariant valid_word: \valid_range(current_word,0,max_string_sz-1) &&
  @ \forall int k; \valid_index(current_word,k) =>
  @   (0 <= current_word[k] < alphabet_sz)
  */

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
  @   0 <= \result <= alphabet_sz &&
  @   \result == current_word[i]
  */
unsigned int get_char(unsigned int i)
{ return current_word[i]; }

/* fresh node allocation function */
/*@ requires next_node < max_nodes_nb
  @ assigns next_node
  @ ensures
  @   \result == nodes_list + \old(next_node) &&
  @   next_node == \old(next_node) + 1
  */
node *get_fresh_node()
{
  node *n = &(nodes_list[next_node]);
  /* note that we don't need to check wether n is NULL or */
  /* not since it is *not*, as required in pre-condition  */
  next_node++;
  return n;
}

/* target research function */
/*@ requires
  @   0 <= c < alphabet_sz &&
  @   \exists int k; (\valid_index(nodes_list,k) && t == nodes_list + k)
  @ ensures
  @   \exists int k; (\valid_index(nodes_list,k) && \result == nodes_list + k)
  */
node *target(node *t,unsigned int c)
{ return t->sons[c]; }

/* suffix head research function */
unsigned int locate_head(node *m, unsigned int i, node **r)
{
  while(get_char(i) != 0)
  {
    node *t = target(m,get_char(i));
    if(t == NULL) break;
    m = t;
    i++;
  }
  *r = m;
  return i;
}

/* node's son insertion function */
void insert_son(node *f, node *s, unsigned int i)
{ f->sons[get_char(i)] = s; }

/* suffix tree construction function */
node *build_suffix_tree()
{
  node *m = get_fresh_node();
  unsigned int i;
  if(m == NULL) return NULL;
  for(i = 0; get_char(i) != 0; i++)
  {
    node *p = NULL;
    unsigned int k = locate_head(m,i,&p);
    unsigned int j;
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

