
/* Schorr-Waite algorithm */

typedef struct struct_node {
  unsigned int m :1;
  unsigned int c :1;
  struct struct_node *l, *r;
} * node;

#define null ((void*)0)

void schorr_waite(node root) {
  node t = root;
  node p = null;
  while (p != null || (t != null && ! t->m)) {
    if (t == null || t->m) {
      if (p->c) {
	/* pop */
	node q = t;
	t = p;
	p = p->r;
	t->r = q;
      } else {
	/* swing */
	node q = t;
	t = p->r;
	p->r = p->l;
	p->l = q;
	p->c = 1;
      }
    } else {
      /* push */
      node q = p;
      p = t;
      t = t->l;
      p->l = q;
      p->m = 1;
      p->c = 0;
    }
  }
}
