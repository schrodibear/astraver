/* oct_private.h
   Include this in order to access to low-level octagon data structures.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */
#ifndef OCT_PRIVATE_H__
#define OCT_PRIVATE_H__

#include <oct.h>

#ifdef __cplusplus
extern "C" {
#endif


/* Shortcuts */
/* --------- */

#define oct_alloc               OCT_PROTO(alloc)
#define oct_full_copy           OCT_PROTO(full_copy)
#define oct_close               OCT_PROTO(close)
#define oct_is_closed           OCT_PROTO(is_closed)
#define oct_close_lazy          OCT_PROTO(close_lazy)
#define oct_check_closed        OCT_PROTO(check_closed)
#define oct_m_elem              OCT_PROTO(m_elem)
#define oct_close_incremental   OCT_PROTO(close_incremental)

#ifdef OCT_USE_TAG
#define oct_close_sub           OCT_PROTO(close_sub)
#define oct_close_full          OCT_PROTO(close_full)
#define oct_close_incremental_copy   OCT_PROTO(close_incremental_copy)
#endif


/************/
/* Octagons */
/************/

/*
  Unlike the presentation of the article "The Octagonal Abstract Domain",
  there is no redundancy in the internal representation of the invariants.
  This is achevied by storing m[i][j] only if i>=j or i=j^1.
  There is no loss of information because, by coherence, m[j^1][i^1]=m[i][j].
  In memory, the matrix has approximately the form of a triangle:

      j ->  0 1 2 3 4 5
            ___
        0  |_|_|
        1  |_|_|___
  i ->  2  |_|_|_|_|
        3  |_|_|_|_|___
        4  |_|_|_|_|_|_|
        5  |_|_|_|_|_|_|

  In the following we will use the term 'matrix' even if the representation
  no longer has a matrix form.
  The elements are stored in a flat array with m[i][j] beeing stored in
  c[j+((i+1)*(i+1))/2].

  There is no longer an emptyness test as emptyness is tested during the
  closure.

  Memory managment is a little complex in order to avoid unnecessary copy,
  closure or emptyness checking.
  All operators come in 2 forms: a copy form that protects all arguments,
  and a in-place form that destroys the arguments and is more efficient.
  There is also reference counting so that copy versions of operators can
  return the one of the argument without having to copy it (union when one
  argument is empty, for example).
  This results in a lazy copy-on-write policy saying that we must perform
  an actual copy only when modifing in-place a matrix that have a
  reference count > 1.
  The last mechanism is remembering of closure form. When the argument of
  an operator must be closed, but must stay accessible in its original form
  (either we use the copy form of the operator, or the argument has a
  reference count > 1); we keep the closed form in memory and add a pointer
  from the original unchanged argument to its closed form we just computed.
  If the arguement is used again with an operator requiring the normal form,
  the stored form is reused and no extra closure algorithm is performed.
  (this mechanism can be turned off manually if we are short of memory,
  this can result in time inefficiency).

*/

/* nb of elements in a matrix with n variables */
#define matsize(n)   (2*(size_t)(n)*((size_t)(n)+1))

/* xj - xi <= m->c[matpos(i,j)], if j/2 <= i/2 */
#define matpos(i,j)  ((size_t)(j)+(((size_t)(i)+1)*((size_t)(i)+1))/2)

/* xj - xi <= m->c[matpos2(i,j)] for all i,j */
#define matpos2(i,j) ((j)>(i)?matpos(((j)^1),((i)^1)):matpos(i,j))

/* state of a matrix representing an octagon */
typedef enum {
  OCT_EMPTY  = 0,         /* empty domain */
  OCT_NORMAL = 1,           
  OCT_CLOSED = 2
} oct_state;


#ifdef OCT_USE_TAG

  /* underlying type for tag slots, a tag is a bit in a slot */
typedef unsigned char oct_tag_t;

  /* size of the array of tags in an octagon with n variables */
#define tagsize(n)   (((size_t)(matsize(n))-1)/8+1)
  /* number of tags set in a tag slot */
#define tag_count(t) (((t)&1) + (((t)>>1)&1) + (((t)>>2)&1) + (((t)>>3)&1) \
  + (((t)>>4)&1) + (((t)>>5)&1) + (((t)>>6)&1) + (((t)>>7)&1))

  /* retrieves [k]'th tag under pointer [pt] */
#define tag_get(pt,k)    (((pt)[(size_t)(k)/8] >> ((size_t)(k)%8)) &1)
  /* flips [k]'th tag under pointer [pt] */
#define tag_flip(pt,k)   ((pt)[(size_t)(k)/8] ^= (1<<((size_t)(k)%8)))
  /* set [k]'th tag (to 1) under pointer [pt] */
#define tag_set(pt,k)    ((pt)[(size_t)(k)/8] |= (1<<((size_t)(k)%8)))
  /* unset [k]'th tag (to 0) under pointer [pt] */
#define tag_unset(pt,k)  ((pt)[(size_t)(k)/8] &= ~(1<<((size_t)(k)%8)))

  /* initializes [a] pointing to [n] tag slots */
#define tag_init_n(a,n)  memset((a),0,sizeof(oct_tag_t)*(n))
  /* copies [n] tag slots from pointer [a] to pointer [b] */
#define tag_set_n(a,b,n) memcpy((a),(b),sizeof(oct_tag_t)*(n))

#endif /* OCT_USE_TAG */


#ifdef OCT_USE_TAG

  /* to be used as [oper] parameter of TAG_OPER */
#define TAG_EQUAL(dest,src) (dest) = (src)

  /* oper should not be parenthesized as it is a macro */
#define TAG_OPER(oper,tagged,dest,src,tc,i) \
  do { \
    if ((tagged) && tag_get((tc),(i))) num_set_infty(dest); \
    else oper((dest),(src)+(i)); \
  } while (0)

#define TAG_OPER2(oper,tagged,dest,src,tc,i,inf) \
  do { \
    if ((tagged) && tag_get((tc),(i))) oper((dest),(inf)); \
    else oper((dest),(src)+(i)); \
  } while (0)

  /* tagged constraint is replaced by tighter one.
     parameters:
       tagged: current octagon being tagged or not (shortcut)
       cur:    current constraint value
       new:    possible new constraint value
       tc:     array of tags of the result octagon
       i:      position of the constraint
  */
#define TAG_FROM_MIN(tagged,cur,new,tc,i) \
  do { \
    if (tagged) { \
      if ((! num_min_is_left((cur),(cur),(new))) && tag_get((tc),(i))) { \
	tag_flip((tc),(i)); \
      } \
    } \
    else num_min((cur),(cur),(new)); \
  } while (0)

#define TAG_DEF(tagged,tag,tc,i) \
  bool (tag) = (tagged) && tag_get((tc),(i));

#define TAG_FROM_MIN2(tagged,cur,new,tcur,tnew) \
  do { \
    if (tagged) { \
      if (! num_min_is_left((cur),(cur),(new))) { \
	(tcur) = (tnew); \
      } \
    } \
    else num_min((cur),(cur),(new)); \
  } while (0)

#define TAG_FROM_MIN3(tagged,cur,new,tc,curi,newtag) \
  do { \
    if (tagged) { \
      if ((! num_min_is_left((cur),(cur),(new))) \
          && (tag_get((tc),(curi)) != (newtag))) { \
	tag_flip((tc),(curi)); \
      } \
    } \
    else num_min((cur),(cur),(new)); \
  } while (0)

#define TAG_FROM_MIN4(tagged,cur,new,tc,curi,newi) \
  do { \
    if (tagged) { \
      if ((! num_min_is_left((cur),(cur),(new))) \
          && (tag_get((tc),(curi)) != tag_get((tc),(newi)))) { \
	tag_flip((tc),(curi)); \
      } \
    } \
    else num_min((cur),(cur),(new)); \
  } while (0)

  /* result constraint is copied from [a].
     [a] and [b] are two octagons not passed as parameters.
     parameters:
       tagged: current octagon being tagged or not (shortcut)
       is_new: result octagon was freshly allocated
       is_b:   result octagon is [b] or a copy of [b]
       ta:     array of tags of [a]
       tb:     array of tags of [b]
       tc:     array of tags of the result octagon
       i:      position of the constraint     
  */
#define TAG_FROM_A(tagged,is_new,is_b,ta,tb,tc,i) \
  do { \
    if (tagged) { \
      if ((is_new) && tag_get((ta),(i))) { \
        tag_set((tc),(i)); \
      } \
      else if ((is_b) && (tag_get((ta),(i)) != tag_get((tb),(i)))) { \
        tag_flip((tc),(i)); \
      } \
    } \
  } while (0)

  /* result constraint is copied from [b].
     [a] and [b] are two octagons not passed as parameters.
     parameters:
       tagged: current octagon being tagged or not (shortcut)
       is_new: result octagon was freshly allocated
       is_a:   result octagon is [a] or a copy of [a]
       ta:     array of tags of [a]
       tb:     array of tags of [b]
       tc:     array of tags of the result octagon
       i:      position of the constraint     
  */
#define TAG_FROM_B(tagged,is_new,is_a,ta,tb,tc,i) \
  TAG_FROM_A(tagged,is_new,is_a,tb,ta,tc,i)

  /* result constraint is copied from a bound or threshold.
     parameters:
       tagged: current octagon being tagged or not (shortcut)
       is_new: result octagon was freshly allocated
       tc:     array of tags of the result octagon
       i:      position of the constraint     
  */
#define TAG_FROM_BOUND(tagged,is_new,tc,i) \
  do { \
    if ((tagged) && (! (is_new))) tag_unset((tc),(i)); \
  } while (0)

  /* result constraint is copied from a constraint (tagged or not).
     [a] is the current octagon.
     parameters:
       tagged: current octagon being tagged or not (shortcut)
       ta:     array of tags of [a]
       tc:     array of tags of the result octagon
       cons:   new constraint
       i:      position of the constraint     
  */
#define TAG_FROM_CONS(tagged,ta,tc,cons,i) \
  do { \
    (tagged) = ((tagged) || (cons).tagged); \
    if (tagged) { \
      if (tag_get((ta),(i)) != (cons).tagged) { \
        tag_flip((tc),(i)); \
      } \
    } \
  } while (0)

  /* introduces [tagged] for the current octagon.
     parameters:
       a:      current octagon
       tagged: current octagon being tagged or not (shortcut)
  */
#define TAG_INTRO_TAGGED1(a,tagged) \
  bool (tagged) = (a)->tagged;

  /* introduces [tagged] for two octagons.
     parameters:
       a:      first octagon
       b:      second octagon
       tagged: either octagon being tagged or not (shortcut)
  */
#define TAG_INTRO_TAGGED2(a,b,tagged) \
  bool (tagged) = ((a)->tagged || (b)->tagged);

  /* introduces [tagged], [ta] and [tc] for the current octagon.
     parameters:
       a:      current octagon
       ta:     array of tags of [a]
       tc:     array of tags of the result octagon
       tagged: current octagon being tagged or not (shortcut)
  */
#define TAG_INTRO1(a,ta,tc,tagged) \
  oct_tag_t* (ta) = (a)->tags; \
  oct_tag_t* (tc); \
  TAG_INTRO_TAGGED1(a,tagged)

#define TAG_INTRO_NO_TAGGED1(a,ta,tc,tagged) \
  oct_tag_t* (ta) = (a)->tags; \
  oct_tag_t* (tc); \
  (tagged) = (a)->tagged;

  /* introduces [tagged], [ta], [tb], [tc], [is_a], [is_b] and [is_new].
     parameters:
       a:      first octagon
       b:      second octagon
       is_a:   result octagon is [a] or a copy of [a]
       is_b:   result octagon is [b] or a copy of [b]
       is_new: result octagon was freshly allocated
       ta:     array of tags of [a]
       tb:     array of tags of [b]
       tc:     array of tags of the result octagon
       tagged: current octagon being tagged or not (shortcut)
  */
#define TAG_INTRO2(a,b,is_a,is_b,is_new,ta,tb,tc,tagged) \
  oct_tag_t* (ta) = (a)->tags; \
  oct_tag_t* (tb) = (b)->tags; \
  oct_tag_t* (tc); \
  bool (is_a) = 0, (is_b) = 0, (is_new) = 0; \
  TAG_INTRO_TAGGED2(a,b,tagged)

  /* set a boolean variable.
     parameters:
       v:      boolean variable to set
  */
#define TAG_UPDATE(v) \
  do { \
    v = 1; \
  } while (0)

  /* defines [tc] to be the array of tags of the result octagon [r].
     parameters:
       tc:     array of tags of the result octagon
       r:      result octagon
       is_new: result octagon was freshly allocated
  */
#define TAG_DEF_TC(tc,r,is_new) \
  do { \
    (tc) = (r)->tags; \
    if (is_new) { \
      tag_init_n((r)->tags,tagsize((r)->n)); \
    } \
  } while (0)

  /* updates [r->tagged] after result octagon [r] has been computed.
     parameters:
       r:      result octagon
       tagged: current octagon(s) being tagged or not (shortcut)
  */
#define TAG_DEF_TAGGED(r,istagged) \
  do { \
    (r)->tagged = ((istagged) && oct_hastags(r)) ? true : false; \
  } while (0)

  /* swaps two tags.
     parameters:
       tagged: current octagon being tagged or not (shortcut)
       tc:     array of tags of the result octagon
       i:      first position to swap
       j:      second position to swap       
  */
#define TAG_SWAP(tagged,tc,i,j) \
  do { \
    if (tagged) { \
      if (tag_get((tc),(i)) != tag_get((tc),(j))) { \
        tag_flip((tc),(i)); \
        tag_flip((tc),(j)); \
      } \
    } \
  } while (0)

#define TAG_DEBUG(msg,r) \
  do { \
    if (!(r)->tagged && oct_hastags(r)) { \
      printf(msg "\n"); \
      exit(1); \
    } \
  } while (0)

#else /* ! defined(OCT_USE_TAG) */

#define TAG_OPER(oper,tagged,dest,src,tc,i) \
  do { \
    oper((dest),(src)+(i)); \
  } while (0)

#define TAG_OPER2(oper,tagged,dest,src,tc,i,inf) \
  do { \
    oper((dest),(src)+(i)); \
  } while (0)

  /* tagged constraint is replaced by tighter one.
     parameters used:
       cur:    current constraint value
       new:    possible new constraint value
  */
#define TAG_FROM_MIN(tagged,cur,new,tc,i) \
  do { \
    num_min((cur),(cur),(new)); \
  } while (0)

  /* all other TAG_ macros expand to nothing */
#define TAG_FROM_A(tagged,is_new,is_b,ta,tb,tc,i)
#define TAG_FROM_B(tagged,is_new,is_a,ta,tb,tc,i)
#define TAG_FROM_BOUND(tagged,is_new,tc,i)
#define TAG_FROM_CONS(tagged,ta,tc,cons,i)
#define TAG_INTRO_TAGGED1(a,tagged)
#define TAG_INTRO_TAGGED2(a,b,tagged)
#define TAG_INTRO1(a,ta,tc,tagged)
#define TAG_INTRO_NO_TAGGED1(a,ta,tc,tagged)
#define TAG_INTRO2(a,b,is_a,is_b,is_new,ta,tb,tc,tagged)
#define TAG_UPDATE(v)
#define TAG_DEF_TC(tc,r,is_new)
#define TAG_DEF_TAGGED(r,tagged)
#define TAG_SWAP(tagged,tc,i,j)
#define TAG_DEBUG(msg,r)

#endif /* OCT_USE_TAG */

/* octagon data structure */
struct oct_tt {
  var_t          n;       /* number of variables, aka dimension */

  int            ref;     /* reference counting */

  oct_state      state;   /* is it empty, closed, etc. ? */
  struct oct_tt* closed;  /* pointer to the closed version, or NULL */

  num_t*         c;       /* the matrix, contains matsize(n) elements */

#ifdef OCT_USE_TAG
  bool           tagged;  /* is it tagged ? */
  oct_tag_t*     tags;    /* the bit-array of tags */
#endif
};

/* private because not really useful for user */
oct_t* OCT_PROTO(alloc)     (var_t  n);   /* c allocated but not initialized */
oct_t* OCT_PROTO(full_copy) (oct_t* m);   /* new copy with ref=1 */

/* strong closure */
oct_t* OCT_PROTO(close)      (oct_t* m, bool destructive, bool cache); 
bool   OCT_PROTO(is_closed)  (oct_t* m);
oct_t* OCT_PROTO(close_lazy) (oct_t* m, bool destructive);

bool   OCT_PROTO(check_closed) (const oct_t* m, bool quiet);  /* for debugging purpose */
void OCT_PROTO(close_incremental)  (oct_t* m, var_t v);

#ifdef OCT_USE_TAG
oct_t* OCT_PROTO(close_sub)      (oct_t* m, const num_t* v, bool destructive, bool cache); 
oct_t* OCT_PROTO(close_full)      (oct_t* m, bool destructive, bool cache); 
oct_t* OCT_PROTO(close_incremental_copy)  (oct_t* m, var_t v, bool destructive);
#endif

/* low-level access to an element 
   get the element m[i][j]            */
static inline
num_t*
oct_elem (oct_t* m,
	  var_t  i,
	  var_t  j)
{
  OCT_ASSERT(m->c,"matrix not allocated in oct_elem");
  OCT_ASSERT(i<2*m->n && j<2*m->n,"invalid index in oct_elem");
  return m->c+matpos2(i,j);
}

#ifdef OCT_USE_TAG
/* low-level access to a tag 
   get the tag for m[i][j]            */
static inline
bool
oct_tag (oct_t* m,
	 var_t  i,
	 var_t  j)
{
  OCT_ASSERT(m->tags,"tag array not allocated in oct_tag");
  OCT_ASSERT(i<2*m->n && j<2*m->n,"invalid index in oct_tag");
  return tag_get(m->tags,matpos2(i,j));
}
#endif

/* Octagon in hollow form, 
   cannot be modified in-place !
*/

struct moct_tt {
  var_t     n;     /* number of variables */
  
  size_t*   bol;   /* begin-of-line indices, array of n*2+1 indices */
  var_t*    col;   /* column indices, array of bol[n*2] elements */
  num_t*    data;  /* constraint array of bol[n*2] elements */
  /* data[i] contains the original matrix element at position
       col[i],
       line l, such that bol[l] <= i < bol[l+1]
   */
#ifdef OCT_USE_TAG
  bool           tagged;  /* is it tagged ? */
  oct_tag_t*     tags;    /* the bit-array of tags */
#endif
  /* all fields are NULL if the octagon is empty */
};


/* no direct access, O(log n) time cost */
num_t* OCT_PROTO(m_elem) (moct_t* a, var_t i, var_t j);


/**********/
/* Memory */
/**********/

/* a memory monitor */
struct mmalloc_tt
{
  int    id;         /* incremented after a reset */

  int    nb_alloc;   /* nb of calls to malloc */
  int    nb_realloc; /* nb of calls to realloc */
  int    nb_free;    /* nb of calls to free */

  size_t rem;        /* memory consumption */
  size_t max;        /* max memory consumption */
  size_t tot;        /* total allocated */

};




#ifdef __cplusplus
}
#endif

#endif
