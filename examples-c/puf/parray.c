
/* persistent arrays */

/* manually translated from ocaml code */

enum tag { Diff, Array };

struct data;
struct ref { 
  struct data *contents; 
};
struct data { 
  enum tag tag;
  /*should be a union*/
  int idx; int val; struct ref *next;
  int arr[100];
};

typedef struct ref ref;
 
/*@ predicate is_parray(ref *p) 
    reads 
      p->contents, p->contents->tag, p->contents->idx, p->contents->val,
      p->contents->arr[..], p->contents->next */

/*@ axiom is_parray_def:
    \forall ref *p; 
    is_parray(p) <=> 
       (\valid(p) && \valid(p->contents) &&
        (  (p->contents->tag==Array && \valid_range(p->contents->arr,0,99))
        || (p->contents->tag==Diff && 0<=p->contents->idx<100 &&
            is_parray(p->contents->next))))
*/
 
/*@ predicate In(ref *p, int i, int v) 
    reads 
      p->contents, p->contents->tag, p->contents->idx, p->contents->val,
      p->contents->arr[..], p->contents->next
*/

/*@ axiom In_def:  
      \forall ref *p; \forall int i; \forall int v;
      In(p,i,v) <=>
        (  (p->contents->tag==Array && p->contents->arr[i]==v)
        || (p->contents->tag==Diff && 
            ((p->contents->idx == i && p->contents->val == v) ||
             (p->contents->idx != i && In(p->contents->next,i,v)))))
*/

/*@ requires is_parray(p) && 0<=i<100
  @ ensures In(p,i,\result)
  @*/
int get(ref *p, int i) {
  if (p->contents->tag == Array)
    return p->contents->arr[i];
  else /* Diff */
    if (p->contents->idx == i)
      return p->contents->val;
    else
      return get(p->contents->next,i);
}


/*@ requires is_parray(p) && 0<=i<100
  @ ensures 
      (* is_parray(p) i.e. *)
       (\valid(p) && \valid(p->contents) &&
        (  (p->contents->tag==Array && \valid_range(p->contents->arr,0,99))
        || (p->contents->tag==Diff && 0<=p->contents->idx<100 &&
            is_parray(p->contents->next))))
   && (* is_parray(\result) i.e *)
       (\valid(\result) && \valid(\result->contents) &&
        (  (\result->contents->tag==Array && 
	    \valid_range(\result->contents->arr,0,99))
        || (\result->contents->tag==Diff && 0<=\result->contents->idx<100 &&
            is_parray(\result->contents->next))))
   && In(\result,i,v)
  @*/
ref* set(ref *p, int i, int v) {
  if (p->contents->tag == Array) {
    int old = p->contents->arr[i];
    struct data *new_arr = (struct data*)malloc(sizeof(struct data));
    struct data *new_diff = (struct data*)malloc(sizeof(struct data));
    ref *res = (ref*)malloc(sizeof(ref));
    /* a.(i) <- v */
    p->contents->arr[i] = v;
    /* let res = ref (Array a) */
    res->contents = new_arr;
    new_arr->tag = Array;
    new_arr->arr = p->contents->arr;
    /*@ assert is_parray(res) */
    /* t := Diff (i,old,res) */
    new_diff->tag = Diff;
    new_diff->idx = i;
    new_diff->val = old;
    new_diff->next = res;
    p->contents = new_diff;
    /*@ assert is_parray(p) */
    return res;
  } else {
    struct data *new_diff = (struct data*)malloc(sizeof(struct data));
    ref *res = (ref*)malloc(sizeof(ref));
    /*@ assert is_parray(p) */
    /* ref (Diff (i, v, t)) */
    new_diff->tag = Diff;
    new_diff->idx = i;
    new_diff->val = v;
    new_diff->next = p;
    res->contents = new_diff;
    /*@ assert is_parray(res) */
    return res;
  }
}
	 


/* @ axiom array_is_parray:
    \forall ref *p; 
      \valid(p) => 
      p->contents->tag==Array => 
      \valid_range(p->contents->arr,0,99) => 
      is_parray(p)
*/

