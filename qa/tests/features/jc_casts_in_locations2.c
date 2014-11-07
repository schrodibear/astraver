extern void *malloc(unsigned long size);

struct innermost {
    int a, b;
    char c;
    const char *s;
    void *p;
};

struct inner {
    long long l;
    int a, b;
    struct innermost innermost;
    const char *s;
    void *p;
};

struct outer {
    long long l;
    int a, b;
    struct inner *inner;
    struct innermost *innermost;
    char *s;
    void *p;
};

union inner_and_innermost {
    struct inner inner;
    struct innermost innermost;
};

/*@ requires \typeof(p) <: \type(struct innermost *) && \valid((struct innermost *) p);
  @ assigns ((struct innermost *) p)->a \from ((struct innermost *) p)->b;
  @ ensures \result == \old(((struct innermost *) p)->a);
  @*/
int simple_assigns_field(void *p)
{
    //@ assert p != \null;
    int t = ((struct innermost *) p)-> a; 
    ((struct innermost *) p)-> a = ((struct innermost *) p)-> b;
    return t;
}

//@ assigns ((struct innermost *) p)->a \from ((struct innermost *) p)->b;
int simple_not_assigns_field(void *p)
{
    return 0;
}

//@ assigns \nothing;
int simple_not_assigns_field_correct(void *p)
{
    return 0;
}

/*@ requires \typeof(p) <: \type(struct innermost *) && \valid((struct innermost *) p);
  @ assigns \nothing;
  */
int simple_not_assigns_field_wrong(void *p)
{
    ((struct innermost *) p)-> a = ((struct innermost *) p)-> b;
    return 0;
}

/*
//@ assigns p->inner.p \from (union inner_and_innermost *)p;
void simple_assigns_union(union inner_and_innermost *p)
{
   //void *t = p;
   ((union inner_and_innermost *) p)->inner.p = p;
   //return t;
}

//@ assigns p->inner;
int simple_not_assigns_union(union inner_and_innermost *p)
{
   ((union inner_and_innermost *) p)->inner.p = p;
   return 0;
}
*/

//@ assigns \nothing;
int simple_not_assigns_union_correct(union inner_and_innermost **p)
{
    return 0;
}

/*
//@ assigns \nothing;
int simple_not_assigns_union_wrong(union inner_and_innermost **p)
{
    (*p)->inner.p = *p;
    return 0;
}

//@ assigns p->innermost.p;
void simple_assigns_union_wrong2(union inner_and_innermost *p)
{
    ((union inner_and_innermost *) p)->inner.p = 0;
}
*/

/*@ requires \typeof(p) <: \type(struct outer *);
  @ requires \valid((struct outer *)p) && \valid(((struct outer *)p)->inner);
  @ requires \valid(&((struct outer *)p)->inner->innermost); // STRANGE, BUT CURRENTLY NEEDED!
  @ assigns ((struct outer *) p)->inner->innermost;
  */
int assigns_nested(void *p)
{
    struct innermost *pim = &((struct outer *)p)->inner->innermost;
    
    pim->a = pim->b;
    pim->c = 'c';
    pim->s = "string";
    pim->p = p;
    return 0;
}

//@ assigns ((struct outer *)p)->inner->innermost;
int assigns_nested2(void *p)
{
    return 0;
}


/*@ requires \typeof(p) <: \type (struct outer *);
  @ requires \valid((struct outer *)p) && \valid(((struct outer *)p)->inner);
  @ requires \valid(&((struct outer *)p)->inner->innermost); // STRANGE, BUT CURRENTLY NEEDED!
  @ assigns ((struct outer *)p)->inner->innermost.a, ((struct outer *)p)->inner->innermost.b;
  */
int assigns_nested3(void *p)
{
    struct innermost *pim = &((struct outer *)p)->inner->innermost;
    
    pim->a = pim->b;
    pim->b = 0;
    return pim->a;
}

/*@ requires \typeof(p) <: \type (struct outer *);
  @ requires \valid((struct outer *)p) && \valid(((struct outer *)p)->inner);
  @ requires \valid(&((struct outer *)p)->inner->innermost); // STRANGE, BUT CURRENTLY NEEDED!
  @ assigns \nothing;
 */
int assigns_nested_wrong(void *p)
{
    struct innermost *pim = &((struct outer *)p)->inner->innermost;
    
    pim->a = pim->b;
    return pim->a;
}

/*@ requires \typeof(p) <: \type (struct outer *);
  @ assigns \nothing;
  */
int assigns_nested_correct(void *p)
{
    struct innermost *pim = malloc(sizeof (struct innermost));;
    
    pim->a = pim->b;
    return pim->a;
}

/*@ requires \typeof(p) <: \type (struct outer *);
  @ assigns ((struct outer *)p)->inner->innermost.c;
  */
int assigns_nested_correct2(void *p)
{
    struct innermost *pim = malloc(sizeof (struct innermost));;
    
    pim->a = pim->b;
    return pim->a;
}


/*@ requires \typeof(p) <: \type (struct outer *);
  @ requires \valid((struct outer *)p) && \valid(((struct outer *)p)->inner);
  @ requires \valid(&((struct outer *)p)->inner->innermost); // STRANGE, BUT CURRENTLY NEEDED!
  @ assigns ((struct outer *)p)->inner->innermost;
  */
int assigns_nested_loop(void *p)
{
    struct innermost *pim = &((struct outer *)p)->inner->innermost;
    
    /*@ loop assigns *pim;
      @ loop variant pim->a;
      @ 
     */
    while (pim->a > 0) {
      pim->a--;
      pim->c = 'c';
      pim->s = "string";
      pim->p = p;
    }
    
    return 0;
}

/*@ requires \typeof(p) <: \type (struct outer *);
  @ requires \valid((struct outer *)p) && \valid(((struct outer *)p)->inner);
  @ requires \typeof(((struct outer *)p)->inner->p) <: \type(struct innermost *);
  @ requires \valid(((struct innermost *)((struct outer *)p)->inner->p));
  @ requires ((struct innermost *)((struct outer *)p)->inner->p)->a > 0;
  @ assigns ((struct innermost *)((struct outer *)p)->inner->p)->p, ((struct innermost *)((struct outer *)p)->inner->p)->a;
 */
void assigns_nested_loop2(void *p)
{
  /*@ loop invariant ((struct innermost *)((struct outer *)p)->inner->p)->a > 0;
    @ loop variant ((struct innermost *)((struct outer *)p)->inner->p)->a;*/
  while (--((struct innermost *)((struct outer *)p)->inner->p)->a > 0)
    ((struct innermost *)((struct outer *)p)->inner->p)->p = 0;
}
