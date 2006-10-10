/* oct_test.c
   Test suite for the C library.
   Mosts tests need the NewPolka library support.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#include <math.h>
#include <oct.h>
#include <oct_private.h>

#define TEST_CLOSURE        1
#define TEST_CLOSURE_INCR   1
#define TEST_MINI           1
#define TEST_POLKA          1
#define TEST_POLKA_CONVERT  1
#define TEST_POLKA_INTER    1
#define TEST_POLKA_UNION    1
#define TEST_POLKA_BCONST   1
#define TEST_POLKA_CONST    1
#define TEST_POLKA_INTERV_CONST    1
#define TEST_POLKA_BASSIGN  1
#define TEST_POLKA_ASSIGN   1
#define TEST_POLKA_INTERV_ASSIGN   1
#define TEST_POLKA_BSUBST   1
#define TEST_POLKA_SUBST    1
#define TEST_POLKA_INTERV_SUBST    1
#define TEST_SET_BOUNDS     1
#define TEST_SERIALIZE 1    
#define TEST_SERIALIZE_MINI 1
#define TEST_DIMS           1

/* for profiling, key associated to each polyhedon function */
#define KEY_POLY_IS_INCLUDED_IN 124
#define KEY_POLY_IS_EQUAL 123
#define KEY_POLY_INTERSECTION 122
#define KEY_POLY_CONVEX_HULL 121
#define KEY_POLY_SUBSTITUTE_VARIABLE 120
#define KEY_POLY_ASSIGN_VARIABLE 119
#define KEY_POLY_ADD_CONSTRAINT 118

/**********/
/* Random */
/**********/

/* this is like rand48 */

unsigned long long seed;

void mysrand(long i) 
{
  seed = i;
}

long mylrand()
{
  seed = (0xfdeece66dULL * seed + 0xbULL) & 0x0000ffffffffffffULL;
  return ((long)seed) & 0x7fffffffL;
}

double mydrand()
{
  return (double)(mylrand()%1000000UL) / 1000000.;
}

void random_init()
{
  struct timeval tv;
  gettimeofday (&tv, NULL);
  mysrand (tv.tv_usec);
}





/* In this test, some operators are tested for integrity, others
   are compared to the full matrix version presented in  "The Octagon
   Abstract Domain
*/


/* full matrices */
num_t*
to_full(oct_t* m)
{
  int i,j;
  num_t* f = new_n(num_t,4*m->n*m->n);
  num_init_n(f,4*m->n*m->n);
  for (i=0;i<2*m->n;i++)
    for (j=0;j<2*m->n;j++)
      num_set(f+i*2*m->n+j,oct_elem(m,i,j));
  return f;
}

oct_t*
from_full(num_t* f, int n)
{
  int i,j;
  oct_t* m = oct_alloc(n);
  for (i=0;i<2*n;i++)
    for (j=0;j<2*n;j++)
      num_set(oct_elem(m,i,j),f+i*2*n+j);
  return m;
}

void
full_print (num_t* f, int n)
{
  int i,j;
  for (i=0;i<2*n;i++) {
    if (i) printf("  [ ");
    else   printf("\n[ [ ");
    for (j=0;j<2*n;j++,f++) {
      num_print(f);
      printf(" ");
    }
    if (i<2*n)  printf("]\n");
    else        printf("] ]\n");
  }
}

/* check coherence and diagonal element=0 */
bool
is_ok(num_t* f, int n)
{
  int i,j;
  for (i=0;i<2*n;i++)
    if (num_cmp_int(f+i*2*n+i,0)) return false;
  for (i=0;i<2*n;i++)
    for (j=0;j<2*n;j++)
      if (num_cmp(f+(j^1)*2*n+(i^1),f+i*2*n+j)) return false;
  return true;
}

bool
full_is_eq(num_t* f, num_t* g, int n)
{
  int i,j;
  for (i=0;i<2*n;i++)
    for (j=0;j<2*n;j++,f++,g++)
      if (i!=j && num_cmp(f,g)) return false;
  return true;
}

/* slow implementation of the closure on full matrices */
void
slow_close(num_t* m, int n)
{
  int i,j,k;
  num_t* mm = new_n(num_t,4*n*n);
  num_t a,b,c,d;
  num_init_n(mm,4*n*n);
  num_init(&a); num_init(&b); num_init(&c); num_init(&d);
  for (k=0;k<2*n;k+=2) {
    for (i=0;i<2*n;i++)
      for (j=0;j<2*n;j++) {
	num_add(&a,m+i*2*n+k  ,m+k*2*n+j);
	num_add(&b,m+i*2*n+k+1,m+(k+1)*2*n+j);
	num_add(&c,m+i*2*n+k  ,m+k*2*n+k+1  ); num_add(&c,&c,m+(k+1)*2*n+j);
	num_add(&d,m+i*2*n+k+1,m+(k+1)*2*n+k); num_add(&d,&d,m+k*2*n+j);
	num_min(&a,&a,&b);
	num_min(&c,&c,&d);
	num_min(&a,&a,&c);
	num_min(mm+i*2*n+j,mm+i*2*n+j,&a);
      }
    for (i=0;i<2*n;i++) num_set_int(mm+i*2*n+i,0);
    for (i=0;i<2*n;i++)
      for (j=0;j<2*n;j++) {
	num_div_by_2(&a,mm+i*2*n+(i^1));
	num_div_by_2(&b,mm+(j^1)*2*n+j);
	num_add(&a,&a,&b);
	num_min(mm+i*2*n+j,mm+i*2*n+j,&a);
      }
  }
  num_clear_n(mm,4*n*n);
  num_clear(&a); num_clear(&b); num_clear(&c); num_clear(&d);
  oct_mm_free(mm);
}

/* slow implementation of the emptyness test on full matrices */
bool
is_empty (num_t* m, int n)
{
  int i,j,k;
  num_t* buf = new_n (num_t,2*n);
  num_t a;

  for (i=0;i<2*n;i++) num_init_set_int(buf+i,0);
  num_init(&a);
  
  for (k=0;k<2*n+1;k++)
    for (i=0;i<2*n;i++)
      for (j=0;j<2*n;j++) {
	num_add(&a,buf+i,m+i*2*n+j);
	num_min(buf+j,buf+j,&a);
      }

  for (i=0;i<2*n;i++)
    for (j=0;j<2*n;j++) {
      num_add(&a,buf+i,m+i*2*n+j);
      if (num_cmp(buf+j,&a)>0)
        { num_clear(&a); num_clear_n(buf,2*n); oct_mm_free(buf); return true; }
    }
  
  num_clear(&a); 
  num_clear_n(buf,2*n);
  oct_mm_free (buf);
  return false;
}


/* random domain, n vars, m constraints */
oct_t*
random_oct(int n, int m)
{
  oct_t* a;
  int i;
  OCT_ENTER("[random_oct]",127);
  a = oct_universe(n);
  for (i=0;i<m;i++) {
    int x = mylrand()%(a->n*2);
    int y = mylrand()%(a->n*2);
    if (x!=y) num_set_frac(oct_elem(a,x,y),(mylrand()%20)-4,mylrand()%4+1);
  }
  a->state = OCT_NORMAL;
  OCT_EXIT("[random_oct]",127);
  return a;
}

/* change only line/column v in the octgagon */
void
random_col(oct_t* a, var_t v, int m)
{
  int i;
  OCT_ENTER("[random_col]",126);
  for (i=0;i<m;i++) {
    int x = mylrand()%(a->n*2);
    if (x!=v) num_set_frac(oct_elem(a,x,v),(mylrand()%20)-4,
			   mylrand()%4+1);
  }
  a->state = OCT_NORMAL;
  OCT_EXIT("[random_col]",126);
}


/* returns a random number in [-a,b] */
int 
random_in_inter (num_t* a, num_t* b)
{
  int aa,bb;
  if (num_infty(a) && num_infty(b)) return mylrand()%20 - 10;
  if (num_infty(a)) return num_get_int(b)-(mylrand()%20);
  if (num_infty(b)) return -num_get_int(a)+(mylrand()%20);
  aa = -num_get_int(a);
  bb =  num_get_int(b);
  return aa+((int)(((double)(bb-aa))*mydrand()));
}


/*************/
/* THE TESTS */
/*************/

static int error = 0;
static int nn_, ii_;

static chrono_t chr;

#define NB 60

#define check_begin(n) { int i; ii_=0; nn_=n; printf("  [");\
  for (i=0;i<n;i++) printf("-"); printf("]");\
  for (i=0;i<n+1;i++) printf("%c",8); fflush(stdout);\
  oct_chrono_reset(&chr); oct_chrono_start(&chr); }

#define check_resume() { int i,ii=ii_; check_begin(nn_);\
                         for (i=0;i<ii;i++) check_next('x'); }

#define check_next(c) { ii_++; printf("%c",c); fflush(stdout); }

#define check_end() { printf("\n  (test duration: "); oct_chrono_stop(&chr);\
                      oct_chrono_print(&chr); printf(")\n\n"); }

#define check_warning(s) { error++; printf("\nERROR %s (i=%i)\n",s,i); }



/* closure */


void check_closure()
{
  int N = 30;
  int i;
  printf("Checking closure\n");
#ifndef OCT_NUM_EXACT
  printf("WARNING: the numerical type you've chosen is not exact, this result in sound but approximate emptyness test, equality test, union operator and transfer functions\n");
#endif
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a, *b;
    num_t *A, *B;
    a = random_oct (N,60);
    
    b = oct_close(a,false,false);
    
#ifdef OCT_USE_TAG
    if (!oct_is_included_in(b,a,false)) {
#else
    if (!oct_is_included_in(b,a)) {
#endif
      check_warning("ERROR #1 closed(oct) not less than oct");
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#ifdef OCT_NUM_EXACT
    if (!oct_check_closed(b,true)) {
      check_warning("ERROR #2 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif

#if 0
    if (oct_is_empty(b)) {
      A = to_full(a);
      if (!is_ok(A,N)) {
	check_warning("ERROR #3 inconsistent");
	printf("org = "); oct_print(a);
	printf("F(org) = "); full_print(A,N);
	check_resume();
      }
      if (!is_empty(A,N)) {
	check_warning("ERROR #4 close!=is_empty");
	printf("org = "); oct_print(a);
	printf("F(closed) = "); full_print(A,N);
	check_resume();
      }
      num_clear_n(A,4*N*N); oct_mm_free(A);
      check_next('o');
    }
    else {
      A = to_full(a);
      slow_close(A,N);
      B = to_full(b);
      if (!is_ok(A,N)) {
	check_warning("ERROR #5 inconsistent");
	printf("org = "); oct_print(a);
	printf("closed(F(org)) = "); full_print(A,N);
	check_resume();
      }
      if (!is_ok(B,N)) {
	check_warning("ERROR #6 inconsistent");
	printf("closed = "); oct_print(b);
	printf("F(closed) = "); full_print(B,N);
	check_resume();
      }
      if (is_empty(A,N)) {
	check_warning("ERROR #7 close!=is_empty");
	printf("org = "); oct_print(a);
	printf("closed(F(org)) = "); full_print(A,N);
	check_resume();
      }
      if (!full_is_eq(A,B,N)) {
	check_warning("#8 close!=slow_close");
	printf("org = "); oct_print(a);
	printf("closed = "); oct_print(b);
	printf("closed(F(org)) = "); full_print(A,N);
	printf("F(closed)= "); full_print(B,N);
	check_resume();
      }
      num_clear_n(A,4*N*N); num_clear_n(B,4*N*N); oct_mm_free(A); oct_mm_free(B);
      check_next('*');
    }
#else
      check_next(oct_is_empty(b)?'o':'*');
#endif
    oct_free(a); oct_free(b);
  }
  check_end();
}

void check_closure_incr()
{
  int N = 30;
  int i;
  printf("Checking incremental closure\n");
#ifndef OCT_NUM_EXACT
  printf("WARNING: the numerical type you've chosen is not exact, the result of the incremental closure may differ fromt the result of the closure; they are uncomparable sound approximations of the real closure\n");
#endif
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a, *b, *c;
    var_t v;

    do { a = random_oct (N,50); } while (oct_is_empty(a));
    a = oct_close(a,true,false);
    v = mylrand() % N;
    random_col(a,2*v,  8);
    random_col(a,2*v+1,8);
    b = oct_close(a,false,false);
    c = oct_full_copy(a);
    oct_close_incremental(c,v);
    
    /*    if (oct_is_empty(b)!=oct_is_empty(c)) {
      check_warning("ERROR #1 empty(closed(oct)) not equivalent to empty(closed_incremental(oct))");
      printf("v = %i\n",(int)v);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      printf("closed incremental = "); oct_print(c);
      check_resume();
      }*/
#ifdef OCT_NUM_EXACT
#ifdef OCT_USE_TAG
    if (!oct_is_included_in(b,c,false)) {
#else
    if (!oct_is_included_in(b,c)) {
#endif
      check_warning("ERROR #2 closed(oct) not less than closed_incremental(oct)");
      printf("v = %i\n",(int)v);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      printf("closed incremental = "); oct_print(c);
      check_resume();
    }    
    if (!oct_check_closed(c,true)) {
      check_warning("ERROR #3 oct_check_closed failed");
      printf("v = %i\n",(int)v);
      oct_check_closed(c,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      printf("closed incremental = "); oct_print(c);
      check_resume();
    }
    if (!oct_is_equal(b,c)) {
      check_warning("ERROR #4 closed(oct) != closed_incremental(oct)");
      printf("v = %i\n",(int)v);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      printf("closed incremental = "); oct_print(c);
      check_resume();
    }
#endif
    check_next(oct_is_empty(b)?'o':'*');
    oct_free(a); oct_free(b); oct_free(c);
  }
  check_end();
}

#ifdef OCT_HAS_NEW_POLKA

/* new polka */

poly_t* random_poly(int n, int m)
{
  poly_t* p = poly_universe(n), *r;
  matrix_t* mat = matrix_alloc(m, polka_dec+n, false);
  int i,j;
  OCT_ENTER("[random_poly]",125);
  matrix_clear (mat);
  for (i=0;i<m;i++) {
    pkint_set_si(mat->p[i][0],(mylrand()%4)+1);
    pkint_set_si(mat->p[i][1],(mylrand()%6)-2);
    for (j=0;j<n;j++)
      if (mylrand()%3==0)
	pkint_set_si(mat->p[i][polka_dec+j],(mylrand()%20)-4);
  }
  r = poly_add_constraints (p,mat);
  matrix_free (mat);
  poly_free (p);
  OCT_EXIT("[random_poly]",125);
  return r;
}

void check_polka_convert()
{
  int N = 8;
  int i;
  printf("Checking octagon -> polyhedron conversion.\n");  
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p;

    a = random_oct (N,20);
    p = oct_to_poly (a);
    b = oct_from_poly (p);

#ifdef OCT_NUM_CLOSED
#ifdef OCT_USE_TAG
    if (!oct_is_included_in(a,b,false)) { 
#else
    if (!oct_is_included_in(a,b)) { 
#endif
      check_warning("ERROR #1 oct->poly->oct not bigger than oct"); 
      printf("org = "); oct_print(a);
      printf("poly(org) = "); poly_print(p);
      printf("oct(poly(org)) = "); oct_print(b);
      check_resume();
   }
#endif
#ifdef OCT_NUM_EXACT
    if (!oct_is_equal(a,b)) { 
      check_warning("WARNING #2 oct->poly->oct!=oct"); 
      printf("org = "); oct_print(a);
      printf("poly(org) = "); poly_print(p);
      printf("oct(poly(org)) = "); oct_print(b);
      check_resume();
    }
#endif

    check_next(oct_is_empty(a)?'o':'*');

    oct_free (a); oct_free(b); poly_free (p);
  }
  check_end();

  printf("Checking polyherdon -> octagon conversion.\n");  
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a;
    poly_t *p, *q;

    p = random_poly (N,10);
    a = oct_from_poly (p);
    q = oct_to_poly (a);

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(p,q,false)) {
#else
    if (!poly_is_included_in(p,q)) {
#endif
      check_warning("ERROR #1 poly->oct->poly not bigger than poly");
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("poly(oct(org)) = "); poly_print(q);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);

    check_next(poly_is_empty(p)?'o':'*');

    oct_free (a); poly_free (p); poly_free (q);
  }
  check_end();
}


void check_polka_intersection()
{
  int N = 7;
  int i;
  printf("Checking octagon vs. polyhedron intersection.\n");  
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b, *c;
    poly_t *p, *q, *r, *s;
    bool empty;

    a = random_oct (N,10);
    b = random_oct (N,10);
    empty = oct_is_empty (a) || oct_is_empty(b);
    p = oct_to_poly (a);
    q = oct_to_poly (b);
    oct_free (a);
    oct_free (b);

    OCT_ENTER("[poly_intersection]",KEY_POLY_INTERSECTION);
    r = poly_intersection (p,q);
    OCT_EXIT("[poly_intersection]",KEY_POLY_INTERSECTION);

    a = oct_from_poly (p);
    b = oct_from_poly (q);
    c = oct_intersection (a, b, false);
    s = oct_to_poly (c);

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(r,s,false)) { 
#else
    if (!poly_is_included_in(r,s)) { 
#endif
      check_warning("ERROR #1 oct intersection not bigger than poly intersection"); 
      printf("org1 = "); poly_print(p);
      printf("org2 = "); poly_print(q);
      printf("oct(org1) = "); oct_print(a);
      printf("oct(org2) = "); oct_print(b);
      printf("org1 U org2 = "); poly_print(r);
      printf("oct(org2) U oct(org2)) = "); oct_print(c);
      printf("poly(oct(org2) U oct(org2)) = "); poly_print(s);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_NUM_EXACT
    OCT_ENTER("[poly_is_equal]",KEY_POLY_IS_EQUAL);
    if (!poly_is_equal(r,s)) { 
      check_warning("WARNING #2 oct intersection != poly intersection"); 
      printf("org1 = "); poly_print(p);
      printf("org2 = "); poly_print(q);
      printf("oct(org1) = "); oct_print(a);
      printf("oct(org2) = "); oct_print(b);
      printf("org1 U org2 = "); poly_print(r);
      printf("oct(org2) U oct(org2)) = "); oct_print(c);
      printf("poly(oct(org2) U oct(org2)) = "); poly_print(s);
      check_resume();
    }
    OCT_EXIT("[poly_is_equal]",KEY_POLY_IS_EQUAL);
#endif
    check_next(empty?'.':oct_is_empty(c)?'o':'*');

    oct_free (a); oct_free(b); oct_free (c); 
    poly_free (p); poly_free (q); poly_free (r); poly_free (s);
  }
  check_end();
}


void check_polka_union()
{
  int N = 7;
  int i;
  printf("Checking octagon vs. polyhedron convex hull.\n");  
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b, *c, *d;
    poly_t *p, *q, *r, *s;
    bool empty;

    a = random_oct (N,15);
    b = random_oct (N,10);
    empty = oct_is_empty (a) || oct_is_empty(b);
    a = oct_close (a,true,false);
    b = oct_close (b,true,false);
    p = oct_to_poly (a);
    q = oct_to_poly (b);
    oct_free (a);
    oct_free (b);

    OCT_ENTER("[poly_convex_hull]",KEY_POLY_CONVEX_HULL);
    r = poly_convex_hull (p,q);
    OCT_EXIT("[poly_convex_hull]",KEY_POLY_CONVEX_HULL);
    d = oct_from_poly (r);

    a = oct_from_poly (p);
    b = oct_from_poly (q);
    c = oct_convex_hull (a, b, false);
    s = oct_to_poly (c);

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(r,s,false)) { 
#else
    if (!poly_is_included_in(r,s)) { 
#endif
      check_warning("ERROR #1 oct union not bigger than poly union"); 
      printf("org1 = "); poly_print(p);
      printf("org2 = "); poly_print(q);
      printf("oct(org1) = "); oct_print(a);
      printf("oct(org2) = "); oct_print(b);
      printf("org1 U org2 = "); poly_print(r);
      printf("oct(org2) U oct(org2)) = "); oct_print(c);
      printf("poly(oct(org2) U oct(org2)) = "); poly_print(s);
      printf("oct(poly(oct(org2) U oct(org2))) = "); oct_print(d);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_NUM_EXACT
    if (!oct_check_closed(c,true)) {
      check_warning("ERROR #2 oct_check_closed failed");
      printf("inc = "); oct_print(c);
      check_resume();
    }
    if (!oct_is_equal(c,d)) {
      check_warning("WARNING #3 oct union not best");
      printf("org1 = "); poly_print(p);
      printf("org2 = "); poly_print(q);
      printf("oct(org1) = "); oct_print(a);
      printf("oct(org2) = "); oct_print(b);
      printf("org1 U org2 = "); poly_print(r);
      printf("oct(org2) U oct(org2)) = "); oct_print(c);
      printf("poly(oct(org2) U oct(org2)) = "); poly_print(s);
      printf("oct(poly(oct(org2) U oct(org2))) = "); oct_print(d);
      check_resume();
    }
#endif
    check_next(empty?'.':oct_is_empty(c)?'o':'*');

    oct_free (a); oct_free(b); oct_free (c); oct_free (d); 
    poly_free (p); poly_free (q); poly_free (r); poly_free (s);
  }
  check_end();
}

void check_polka_bin_constraint()
{
  int N = 8;
  int i;
  pkint_t* pc = vector_alloc(N+polka_dec);
  pkint_t one;
  pkint_t mone;
  oct_cons oc;
  pkint_init_set_si (one,   1);
  pkint_init_set_si (mone, -1);
  num_init(&oc.c);
  printf("Checking octagon vs. polyhedron binary unit constraint.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;

    a = random_oct (N,20);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    oc.type = mylrand()%6;
    num_set_int(&oc.c,(mylrand()%30)-5);
    oc.x = mylrand()%N;
    oc.y = mylrand()%N;
    vector_clear (pc,N+polka_dec);
    pkint_set_si(pc[0],1);
    pkint_set_si(pc[1],num_get_int(&oc.c));
    pkint_set_si(pc[polka_dec+oc.x],
		(oc.type==px || oc.type==pxpy || oc.type==pxmy) ? -1 : 1); 
    if (oc.type!=px && oc.type!=mx)
      if (oc.type==pxpy || oc.type==mxpy)
	pkint_add(pc[polka_dec+oc.y], pc[polka_dec+oc.y], mone);
      else
	pkint_add(pc[polka_dec+oc.y], pc[polka_dec+oc.y], one);
    
    OCT_ENTER("[poly_add_constraint]",KEY_POLY_ADD_CONSTRAINT);
    q = poly_add_constraint (p, pc);
    OCT_EXIT("[poly_add_constraint]",KEY_POLY_ADD_CONSTRAINT);

    a = oct_from_poly (p);
    if (mylrand()%2) a = oct_close(a,true,false);
    b = oct_add_bin_constraints (a, 1, &oc, false);
    r = oct_to_poly (b);

#ifdef OCT_NUM_EXACT
    if (b->state==OCT_CLOSED && !oct_check_closed(b,true)) {
      check_warning("ERROR #1 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(q,r,false)) { 
#else
    if (!poly_is_included_in(q,r)) { 
#endif
      check_warning("ERROR #2 constrained oct not bigger than constrained poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("poly constraint = "); vector_print(pc,N+polka_dec);
      printf("oct constraint = x:%i y:%i c:%i type:%i\n",
	     oc.x,oc.y,num_get_int(&oc.c),oc.type);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_NUM_EXACT
    OCT_ENTER("[poly_is_equal]",KEY_POLY_IS_EQUAL);
    if (!poly_is_equal(q,r)) { 
      check_warning("WARNING #3 constrained oct != constrained poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("poly constraint = "); vector_print(pc,N+polka_dec);
      printf("oct constraint = x:%i y:%i c:%i type:%i\n",
	     oc.x,oc.y,num_get_int(&oc.c),oc.type);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_equal]",KEY_POLY_IS_EQUAL);
#endif
    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (q); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  pkint_clear (one);
  pkint_clear (mone);
}

void check_polka_constraint()
{
  int N = 8;
  int i,j;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,N+1);
  num_init_n(oc,N+1);
  printf("Checking octagon vs. polyhedron linear constraint.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c;

    a = random_oct (N,20);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    vector_clear (pc,N+polka_dec);
    for (j=0;j<N;j++) {
      if (mylrand()%3==0) {
	c = (mylrand()%20)-4;
	pkint_set_si(pc[polka_dec+j],c);
	num_set_int(oc+j,c);
      } 
      else num_set_int(oc+j,0);
    }
    pkint_set_si(pc[0],1);
    c = (mylrand()%20)-4;
    pkint_set_si(pc[1],c);
    num_set_int(oc+N,c);
    
    OCT_ENTER("[poly_add_constraint]",KEY_POLY_ADD_CONSTRAINT);
    q = poly_add_constraint (p, pc);
    OCT_EXIT("[poly_add_constraint]",KEY_POLY_ADD_CONSTRAINT);

    a = oct_from_poly (p);
    b = oct_add_constraint (a, oc, false);
    r = oct_to_poly (b);

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(q,r,false)) { 
#else
    if (!poly_is_included_in(q,r)) { 
#endif
      check_warning("ERROR #1 constrained oct not bigger than constrained poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("poly constraint = "); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (q); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,N+1); oct_mm_free (oc);
}


void check_polka_bin_assign()
{
  int N = 8;
  int i,j;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,N+1);
  num_init_n(oc,N+1);
  printf("Checking octagon vs. polyhedron binary unit assignment.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    vector_clear (pc,N+polka_dec);
    for (j=0;j<N;j++) num_set_int(oc+j,0);

    j = mylrand()%N;
    c = (mylrand()%3)-1;
    pkint_set_si(pc[polka_dec+j],c);
    num_set_int(oc+j,c);

    if (mylrand()%3) j = mylrand()%N;

    pkint_set_si(pc[0],1);
    c = (mylrand()%10)-5;
    pkint_set_si(pc[1],c);
    num_set_int(oc+N,c);

    OCT_ENTER("[poly_assign_variable]",KEY_POLY_ASSIGN_VARIABLE);
    q = poly_assign_variable (p, j, pc);
    OCT_EXIT("[poly_assign_variable]",KEY_POLY_ASSIGN_VARIABLE);

    a = oct_from_poly (p);
    if (mylrand()%2) a = oct_close(a,true,false);
    b = oct_assign_variable (a, j, oc, false);
    r = oct_to_poly (b);
 
#ifdef OCT_NUM_EXACT
    if (b->state==OCT_CLOSED && !oct_check_closed(b,true)) {
      check_warning("ERROR #1 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(q,r,false)) { 
#else
    if (!poly_is_included_in(q,r)) { 
#endif
      check_warning("ERROR #2 assigned oct not bigger than assigned poly"); 
      printf("org = "); poly_print(p); 
      printf("oct(org) = "); oct_print(a); 
      printf("assign: v%i = ",j); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_NUM_EXACT
    OCT_ENTER("[poly_is_equal]",KEY_POLY_IS_EQUAL);
    if (!poly_is_equal(q,r)) { 
      check_warning("WARNING #3 assigned oct != assigned poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("assign: v%i = ",j); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_equal]",KEY_POLY_IS_EQUAL);
#endif
    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (q); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,N+1); oct_mm_free (oc);
}

void check_polka_assign()
{
  int N = 8;
  int i,j;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,N+1);
  num_init_n(oc,N+1);
  printf("Checking octagon vs. polyhedron linear assignment.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    vector_clear (pc,N+polka_dec);
    for (j=0;j<N;j++) {
      if (mylrand()%3==0) {
	c = (mylrand()%20)-10;
	pkint_set_si(pc[polka_dec+j],c);
	num_set_int(oc+j,c);
      } 
      else num_set_int(oc+j,0);
    }
    pkint_set_si(pc[0],1);
    c = (mylrand()%10)-5;
    pkint_set_si(pc[1],c);
    num_set_int(oc+N,c);

    j = mylrand()%N;
    
    OCT_ENTER("[poly_assign_variable]",KEY_POLY_ASSIGN_VARIABLE);
    q = poly_assign_variable (p, j, pc);
    OCT_EXIT("[poly_assign_variable]",KEY_POLY_ASSIGN_VARIABLE);

    a = oct_from_poly (p);
    if (mylrand()%2) a = oct_close(a,true,false);
    b = oct_assign_variable (a, j, oc, false);
    r = oct_to_poly (b);

#ifdef OCT_NUM_EXACT
    if (b->state==OCT_CLOSED && !oct_check_closed(b,true)) {
      check_warning("ERROR #1 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif

   OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(q,r,false)) { 
#else
    if (!poly_is_included_in(q,r)) { 
#endif
      check_warning("ERROR #2 assigned oct not bigger than assigned poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a); 
      printf("assign: v%i = ",j); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q); 
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (q); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,N+1); oct_mm_free (oc);
}

void check_polka_interv_assign()
{
  int N = 12;
  int i,j,v,k;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,2*N+2);
  num_init_n(oc,2*(N+1));
  printf("Checking octagon vs. polyhedron interval linear assignment.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c1, c2;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    for (j=0;j<N;j++) {
      if (mylrand()%3==0) {
	c1 = (mylrand()%20)-10;
	c2 = (mylrand()%20)-10;
	if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
	if (mylrand()%5) num_set_int(oc+2*j  , c2); else num_set_infty(oc+2*j);
	if (mylrand()%5) num_set_int(oc+2*j+1,-c1); else num_set_infty(oc+2*j+1);
      } 
      else { num_set_int(oc+2*j,0); num_set_int(oc+2*j+1,0); }
    }
     
    c1 = (mylrand()%20)-10;
    c2 = (mylrand()%20)-10;
    if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
    num_set_int(oc+2*N,   c2);
    num_set_int(oc+2*N+1,-c1);

    v = mylrand()%N;
    
    a = oct_from_poly (p);
    if (mylrand()%2) a = oct_close(a,true,false);
    b = oct_interv_assign_variable (a, v, oc, false);
    r = oct_to_poly (b);

#ifdef OCT_NUM_EXACT
    if (b->state==OCT_CLOSED && !oct_check_closed(b,true)) {
      check_warning("ERROR #1 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif

   for (k=0;k<4;k++) {
      
      vector_clear (pc,N+polka_dec);
      pkint_set_si(pc[0],1);
      pkint_set_si(pc[1],random_in_inter(oc+2*N+1,oc+2*N));
      for (j=0;j<N;j++)
	pkint_set_si(pc[polka_dec+j],random_in_inter(oc+2*j+1,oc+2*j));

      OCT_ENTER("[poly_assign_variable]",KEY_POLY_ASSIGN_VARIABLE);
      q = poly_assign_variable (p, v, pc);
      OCT_EXIT("[poly_assign_variable]",KEY_POLY_ASSIGN_VARIABLE);

      OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
      if (!poly_is_included_in(q,r,false)) { 
#else
      if (!poly_is_included_in(q,r)) { 
#endif
	check_warning("ERROR #2 assigned oct not bigger than assigned poly"); 
	printf("org = "); poly_print(p);
	printf("oct(org) = "); oct_print(a); 
	printf("assign: v%i = ",v); 
	for (j=0;j<=N;j++) {
	  printf("[-"); num_print(oc+2*((j+N)%(N+1))+1);
	  printf(";"); num_print(oc+2*((j+N)%(N+1)));
	  printf("] ");
	}
	printf("\n");
	printf("choice: v%i = ",v); vector_print(pc,N+polka_dec);
	printf("poly result = "); poly_print(q); 
	printf("oct result = "); oct_print(b);
	printf("poly(oct result) = "); poly_print(r);
	check_resume();
      }
      OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
      poly_free (q);
    }

    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,2*N+2); oct_mm_free (oc);
}

void check_polka_interv_subst()
{
  int N = 12;
  int i,j,v,k;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,2*N+2);
  num_init_n(oc,2*(N+1));
  printf("Checking octagon vs. polyhedron interval linear substitution.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c1, c2;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    for (j=0;j<N;j++) {
      if (mylrand()%3==0) {
	c1 = (mylrand()%20)-10;
	c2 = (mylrand()%20)-10;
	if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
	if (mylrand()%5) num_set_int(oc+2*j  , c2); else num_set_infty(oc+2*j);
	if (mylrand()%5) num_set_int(oc+2*j+1,-c1); else num_set_infty(oc+2*j+1);
      } 
      else { num_set_int(oc+2*j,0); num_set_int(oc+2*j+1,0); }
    }
     
    c1 = (mylrand()%20)-10;
    c2 = (mylrand()%20)-10;
    if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
    num_set_int(oc+2*N,   c2);
    num_set_int(oc+2*N+1,-c1);

    v = mylrand()%N;
    
    a = oct_from_poly (p);
    if (mylrand()%2) a = oct_close(a,true,false);
    b = oct_interv_substitute_variable (a, v, oc, false);
    r = oct_to_poly (b);

#ifdef OCT_NUM_EXACT
    if (b->state==OCT_CLOSED && !oct_check_closed(b,true)) {
      check_warning("ERROR #1 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif

   for (k=0;k<4;k++) {
      
      vector_clear (pc,N+polka_dec);
      pkint_set_si(pc[0],1);
      pkint_set_si(pc[1],random_in_inter(oc+2*N+1,oc+2*N));
      for (j=0;j<N;j++)
	pkint_set_si(pc[polka_dec+j],random_in_inter(oc+2*j+1,oc+2*j));

      OCT_ENTER("[poly_substitute_variable]",KEY_POLY_SUBSTITUTE_VARIABLE);
      q = poly_substitute_variable (p, v, pc);
      OCT_EXIT("[poly_substitute_variable]",KEY_POLY_SUBSTITUTE_VARIABLE);

      OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
      if (!poly_is_included_in(q,r,false)) { 
#else
      if (!poly_is_included_in(q,r)) { 
#endif
	check_warning("ERROR #2 assigned oct not bigger than assigned poly"); 
	printf("org = "); poly_print(p);
	printf("oct(org) = "); oct_print(a); 
	printf("subst: v%i = ",v); 
	for (j=0;j<=N;j++) {
	  printf("[-"); num_print(oc+2*((j+N)%(N+1))+1);
	  printf(";"); num_print(oc+2*((j+N)%(N+1)));
	  printf("] ");
	}
	printf("\n");
	printf("choice: v%i = ",v); vector_print(pc,N+polka_dec);
	printf("poly result = "); poly_print(q); 
	printf("oct result = "); oct_print(b);
	printf("poly(oct result) = "); poly_print(r);
	check_resume();
      }
      OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
      poly_free (q);
    }

    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,2*N+2); oct_mm_free (oc);
}

void check_polka_interv_constraint()
{
  int N = 8;
  int i,j,k;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,2*(N+1));
  num_init_n(oc,2*(N+1));
  printf("Checking octagon vs. polyhedron interval linear constraint.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c1,c2;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

     for (j=0;j<N;j++) {
      if (mylrand()%3==0) {
	c1 = (mylrand()%20)-10;
	c2 = (mylrand()%20)-10;
	if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
	if (mylrand()%5) num_set_int(oc+2*j  , c2); else num_set_infty(oc+2*j);
	if (mylrand()%5) num_set_int(oc+2*j+1,-c1); else num_set_infty(oc+2*j+1);
      } 
      else { num_set_int(oc+2*j,0); num_set_int(oc+2*j+1,0); }
    }
     
    c1 = (mylrand()%20)-10;
    c2 = (mylrand()%20)-10;
    if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
    num_set_int(oc+2*N,   c2);
    num_set_int(oc+2*N+1,-c1);

    a = oct_from_poly (p);
    if (mylrand()%2) a = oct_close(a,true,false);
    b = oct_interv_add_constraint (a, oc, false);
    r = oct_to_poly (b);

#ifdef OCT_NUM_EXACT
    if (b->state==OCT_CLOSED && !oct_check_closed(b,true)) {
      check_warning("ERROR #1 oct_check_closed failed");
      oct_check_closed(b,false);
      printf("org = "); oct_print(a);
      printf("closed = "); oct_print(b);
      check_resume();
    }
#endif
    
    for (k=0;k<4;k++) {
      
      vector_clear (pc,N+polka_dec);
      pkint_set_si(pc[0],1);
      pkint_set_si(pc[1],random_in_inter(oc+2*N+1,oc+2*N));
      for (j=0;j<N;j++)
	pkint_set_si(pc[polka_dec+j],random_in_inter(oc+2*j+1,oc+2*j));
      
      OCT_ENTER("[poly_add_constraint]",KEY_POLY_ADD_CONSTRAINT);
      q = poly_add_constraint (p, pc);
      OCT_EXIT("[poly_add_constraint]",KEY_POLY_ADD_CONSTRAINT);
      
      OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
      if (!poly_is_included_in(q,r,false)) { 
#else
      if (!poly_is_included_in(q,r)) { 
#endif
	check_warning("ERROR #2 assigned oct not bigger than assigned poly"); 
	printf("org = "); poly_print(p);
	printf("oct(org) = "); oct_print(a); 
	printf("constraint: 0 <= "); 
	for (j=0;j<=N;j++) {
	  printf("[-"); num_print(oc+2*((j+N)%(N+1))+1);
	  printf(";"); num_print(oc+2*((j+N)%(N+1)));
	  printf("] ");
	}
	printf("\n");
	printf("choice: 0 <= "); vector_print(pc,N+polka_dec);
	printf("poly result = "); poly_print(q); 
	printf("oct result = "); oct_print(b);
	printf("poly(oct result) = "); poly_print(r);
	check_resume();
      }
      OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
      poly_free (q);
    }
    check_next(empty?'.':oct_is_empty(b)?'o':'*');
    
    oct_free (a); oct_free(b);
    poly_free (p); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,2*N+2); oct_mm_free (oc);
}



void check_polka_bin_subst()
{
  int N = 8;
  int i,j;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,N+1);
  num_init_n(oc,N+1);
  printf("Checking octagon vs. polyhedron binary unit substitution.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    vector_clear (pc,N+polka_dec);
    for (j=0;j<N;j++) num_set_int(oc+j,0);

    j = mylrand()%N;
    c = (mylrand()%3)-1;
    pkint_set_si(pc[polka_dec+j],c);
    num_set_int(oc+j,c);

    if (mylrand()%3) j = mylrand()%N;
    
    pkint_set_si(pc[0],1);
    c = (mylrand()%10)-5;
    pkint_set_si(pc[1],c);
    num_set_int(oc+N,c);

    OCT_ENTER("[poly_substitute_variable]",KEY_POLY_SUBSTITUTE_VARIABLE);
    q = poly_substitute_variable (p, j, pc);
    OCT_EXIT("[poly_substitute_variable]",KEY_POLY_SUBSTITUTE_VARIABLE);

    a = oct_from_poly (p);
    a = oct_close (a, true, false);
    b = oct_substitute_variable (a, j, oc, false);
    r = oct_to_poly (b);
    b = oct_close( b, true, false);
 
    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(q,r,false)) { 
#else
    if (!poly_is_included_in(q,r)) { 
#endif
      check_warning("ERROR #1 substitued oct not bigger than substitued poly"); 
      printf("org = "); poly_print(p); 
      printf("oct(org) = "); oct_print(a); 
      printf("assign: v%i = ",j); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_NUM_EXACT
    OCT_ENTER("[poly_is_equal]",KEY_POLY_IS_EQUAL);
    if (!poly_is_equal(q,r)) { 
      check_warning("WARNING #2 substitued oct != substitued poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("assign: v%i = ",j); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_equal]",KEY_POLY_IS_EQUAL);
#endif
    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (q); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,N+1); oct_mm_free (oc);
}

void check_polka_subst()
{
  int N = 8;
  int i,j;
  pkint_t* pc = vector_alloc(N+polka_dec);
  num_t*  oc = new_n(num_t,N+1);
  num_init_n(oc,N+1);
  printf("Checking octagon vs. polyhedron linear substitution.\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t  *a, *b;
    poly_t *p, *q, *r;
    bool empty;
    int c;

    a = random_oct (N,15);
    empty = oct_is_empty (a);
    p = oct_to_poly (a);
    oct_free (a);

    vector_clear (pc,N+polka_dec);
    for (j=0;j<N;j++) {
      if (mylrand()%3==0) {
	c = (mylrand()%20)-10;
	pkint_set_si(pc[polka_dec+j],c);
	num_set_int(oc+j,c);
      } 
      else num_set_int(oc+j,0);
    }
    pkint_set_si(pc[0],1);
    c = (mylrand()%10)-5;
    pkint_set_si(pc[1],c);
    num_set_int(oc+N,c);

    j = mylrand()%N;
    
    OCT_ENTER("[poly_substitute_variable]",KEY_POLY_SUBSTITUTE_VARIABLE);
    q = poly_substitute_variable (p, j, pc);
    OCT_EXIT("[poly_substitute_variable]",KEY_POLY_SUBSTITUTE_VARIABLE);

    a = oct_from_poly (p);
    b = oct_substitute_variable (a, j, oc, false);
    r = oct_to_poly (b);

    OCT_ENTER("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
#ifdef OCT_USE_TAG
    if (!poly_is_included_in(q,r,false)) { 
#else
    if (!poly_is_included_in(q,r)) { 
#endif
      check_warning("ERROR #1 substitued oct not bigger than substitued poly"); 
      printf("org = "); poly_print(p);
      printf("oct(org) = "); oct_print(a);
      printf("assign: v%i = ",j); vector_print(pc,N+polka_dec);
      printf("poly result = "); poly_print(q);
      printf("oct result = "); oct_print(b);
      printf("poly(oct result) = "); poly_print(r);
      check_resume();
    }
    OCT_EXIT("[poly_is_included_in]",KEY_POLY_IS_INCLUDED_IN);
    check_next(empty?'.':oct_is_empty(b)?'o':'*');

    oct_free (a); oct_free(b);
    poly_free (p); poly_free (q); poly_free (r);
  }
  check_end();
  vector_free(pc,N+polka_dec);
  num_clear_n(oc,N+1); oct_mm_free (oc);
}

void check_polka()
{
  const char* polka_num[] = { "", "long", "long long", "GMP" };
  printf("NewPolka library support enabled with POLKA_NUM = %s (%i).\n\n",polka_num[POLKA_NUM],POLKA_NUM);
#ifndef OCT_NUM_EXACT
  printf("WARNING: the numerical type you've chosen is not exact, conversion to/from polyhedron will induce a sound overapproximation\n\n");
#endif
  polka_initialize(false,2000,2000);
  if (TEST_POLKA_CONVERT) check_polka_convert();
  if (TEST_POLKA_INTER)   check_polka_intersection();
  if (TEST_POLKA_UNION)   check_polka_union();
  if (TEST_POLKA_BCONST)  check_polka_bin_constraint();
  if (TEST_POLKA_CONST)   check_polka_constraint();
  if (TEST_POLKA_BASSIGN) check_polka_bin_assign();
  if (TEST_POLKA_ASSIGN)  check_polka_assign();
  if (TEST_POLKA_INTERV_ASSIGN) check_polka_interv_assign();
  if (TEST_POLKA_INTERV_SUBST)  check_polka_interv_subst();
  if (TEST_POLKA_INTERV_CONST)  check_polka_interv_constraint();
  if (TEST_POLKA_BSUBST)  check_polka_bin_subst();
  if (TEST_POLKA_SUBST)   check_polka_subst();
}

#else
void check_polka()
{
  printf("NewPolka library support not compiled in => won't check octagon/polyhedron interface\n");
}
#endif


void check_mini()
{
  int N = 30;
  int i;
  printf("Checking minimal form\n");
#ifndef OCT_NUM_EXACT
  printf("WARNING: the numerical type you've chosen is not exact, minimal form will induce a sound overapproximation\n");
#endif
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a, *b;
    moct_t* m, *n;
    a = random_oct (N, 60);
    m = oct_m_from_oct (a);
    b = oct_m_to_oct (m);
    n = oct_m_from_oct (b);

#ifdef OCT_USE_TAG
    if (!oct_is_included_in(a,b,false)) { 
#else
    if (!oct_is_included_in(a,b)) { 
#endif
      check_warning("ERROR #1 oct->moct->oct not greater than oct"); 
      printf("org = "); oct_print(a);
      printf("m(org) = "); oct_m_print(m);
      printf("oct(m(org)) = "); oct_print(b);
      check_resume();
    }
    if (oct_is_empty(a)!=oct_m_is_empty(m))
      check_warning("ERROR #2 oct->moct empty != oct empty");
    
    if (!oct_m_is_equal(m,n)) {
      check_warning("ERROR #3 oct->moct->oct->moct != oct->moct");
      printf("m(org) = "); oct_m_print(m);
      printf("m(o(m(org))) = "); oct_m_print(n);
    }
    
#ifdef OCT_NUM_EXACT
    if (!oct_is_equal(a,b)) { 
      check_warning("ERROR #4 oct->moct->oct != oct"); 
      printf("org = "); oct_print(a);
      printf("m(org) = "); oct_m_print(m);
      printf("oct(m(org)) = "); oct_print(b);
      check_resume();
   }
#endif								       

    check_next(oct_is_empty(a)?'o':'*');
    oct_free(a); oct_free(b); oct_m_free(m); oct_m_free(n);
  }
  check_end();
}

void check_set_bounds()
{
  int N = 30;
  int i;
  num_t l,h;
  num_init(&l); num_init(&h);
  printf("Checking set bounds\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a, *b, *c;
    int   c1,c2,v;
    oct_cons s[2];
    
    c1 = (mylrand()%20)-10;
    c2 = (mylrand()%20)-10;
    v = mylrand() % N;
    if (c2<c1) { int tmp=c1; c1=c2; c2=tmp; }
    num_set_int(&h, c2);
    num_set_int(&l,-c1);

    s[0].x=v; s[0].type=px; num_init_set(&s[0].c,&h);
    s[1].x=v; s[1].type=mx; num_init_set(&s[1].c,&l);

    a = random_oct (N, 60);
    b = oct_forget (a,v,false);
    b = oct_add_bin_constraints(b,2,s,true);
    c = oct_set_bounds(a,v,&h,&l,false);

#ifdef OCT_USE_TAG
    if (!oct_is_included_in(b,c,false)) {
#else
    if (!oct_is_included_in(b,c)) {
#endif
      check_warning("ERROR #1 forget+constraints not included in set_bounds");
      printf("org = "); oct_print(a);
      printf("constrained(org) = "); oct_print(b);
      printf("set_bounds(org) = "); oct_print(c);
    }
#ifdef OCT_NUM_EXACT
    if (!oct_is_equal(b,c)) {
      check_warning("ERROR #2 set_bounds != forget+constraints"); 
      printf("org = "); oct_print(a);
      printf("constrained(org) = "); oct_print(b);
      printf("set_bounds(org) = "); oct_print(c);
    }
    if (c->state==OCT_CLOSED && !oct_check_closed(c,true)) {
      check_warning("ERROR #3 oct_check_closed failed");
      oct_check_closed(c,false);
      printf("org = "); oct_print(a);
      printf("set_bounds(org) = "); oct_print(c);
      check_resume();
    }
#endif

    check_next(oct_is_empty(a)?'o':'*');
    oct_free(a); oct_free(b); oct_free(c);
  }
  num_clear(&l); num_clear(&h);
  check_end();
}

void check_serialize()
{
  int N = 30;
  int i;
  printf("Checking serialization\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a, *b;
    void* data, *data2;
    size_t size;
    a = random_oct (N, 80);
    data = oct_serialize(a,&size);
    data2 = new_n(unsigned char*,size);
    memcpy(data2,data,size);
    b = oct_deserialize(data2);
    if (!oct_is_equal(a,b)) {
      check_warning("ERROR #1 deserialize(serialize(org))!= org"); 
      printf("org = "); oct_print(a);
      printf("d(s(oct)) = "); oct_print(b);
    }
    check_next(oct_is_empty(a)?'o':'*');
    oct_mm_free(data);
    oct_mm_free(data2);
    oct_free(a);
    oct_free(b);
  }    
  check_end();
}


void check_serialize_mini()
{
  int N = 30;
  int i;
  printf("Checking serialization of minimal form\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a;
    moct_t *b, *c;
    void* data, *data2;
    size_t size;
    a = random_oct (N, 80);
    b = oct_m_from_oct (a);
    data = oct_m_serialize(b,&size);
    data2 = new_n(unsigned char*,size);
    memcpy(data2,data,size);
    c = oct_m_deserialize(data2);
    if (!oct_m_is_equal(b,c)) {
      check_warning("ERROR #1 deserialize(serialize(org))!= org"); 
      printf("org = "); oct_m_print(b);
      printf("d(s(oct)) = "); oct_m_print(c);
    }
    check_next(oct_m_is_empty(b)?'o':'*');
    oct_mm_free(data);
    oct_mm_free(data2);
    oct_free(a);
    oct_m_free(b);
    oct_m_free(c);
  }    
  check_end();
}


void check_dims()
{
  int N = 15;
  int i;
  printf("Checking add/remove dimensions at arbitrary positions\n");
  check_begin(NB);
  for (i=0;i<NB;i++) {
    oct_t *a, *b, *c, *d;
    dimsup_t add[10], del[10];
    int i,n;
    n = (mylrand()%3)+1;
    for (i=0;i<n;i++) {
      add[i].pos = mylrand()%4;
      if (i>0) add[i].pos += add[i-1].pos; /* ensure increasing */
      add[i].nbdims = mylrand()%4;

      del[i].pos = add[i].pos;
      if (i>0) del[i].pos += (del[i-1].pos-add[i-1].pos) + add[i-1].nbdims;
      del[i].nbdims = add[i].nbdims;
    }
    a = random_oct (N, 80);
    b = oct_add_dimensions_and_project_multi(a,add,n,false);
    c = oct_remove_dimensions_multi(b,del,n,false);
    d = oct_add_dimensions_and_project_multi(c,add,n,false);
    if (!oct_is_equal(a,c)) {
      check_warning("ERROR #1 remove_dims(add_dims(org))!= org"); 
      printf("add vector = [ ");
      for (i=0;i<n;i++)	printf("%i at %i, ",add[i].nbdims, add[i].pos);
      printf("]\n");
      printf("del vector = [ ");
      for (i=0;i<n;i++)	printf("%i at %i, ",del[i].nbdims, del[i].pos);
      printf("]\n");
      printf("org = "); oct_print(a);
      printf("add_dims(org) = "); oct_print(b);
      printf("remove_dims(add_dims(org)) = "); oct_print(c);
    }
    if (!oct_is_equal(b,d)) {
      check_warning("ERROR #2 add_dims(remove_dims(org))!= org"); 
      printf("add vector = [ ");
      for (i=0;i<n;i++)	printf("%i at %i, ",add[i].nbdims, add[i].pos);
      printf("]\n");
      printf("del vector = [ ");
      for (i=0;i<n;i++)	printf("%i at %i, ",del[i].nbdims, del[i].pos);
      printf("]\n");
      printf("org = "); oct_print(b);
      printf("remove_dims(org) = "); oct_print(c);
      printf("add_dims(remove_dims(org)) = "); oct_print(d);
    }
    check_next(oct_is_empty(a)?'o':'*');
    oct_free(a); oct_free(b); oct_free(c); oct_free(d);
  }    
  check_end();
}



int
main (int argc, char**argv)
{
  chrono_t chr;
  oct_init();
  random_init();
  oct_chrono_reset(&chr); oct_chrono_start(&chr);
  printf("Numerical domain: %s\nUnderlying implementation: %s\n\n",
	 oct_domain_string[OCT_DOMAIN],
	 OCT_IMPLEMENTATION_STRING);
  if (TEST_CLOSURE) check_closure();
  if (TEST_CLOSURE_INCR) check_closure_incr();
  if (TEST_MINI) check_mini();
  if (TEST_POLKA) check_polka();
  if (TEST_SET_BOUNDS) check_set_bounds();
  if (TEST_SERIALIZE) check_serialize();
  if (TEST_SERIALIZE_MINI) check_serialize_mini();
  if (TEST_DIMS) check_dims();
  if (error) printf("\n\nTEST FAILED with %i error(s)!\n\n",error);
  else       printf("\n\nTEST PASSED\n\n");
  oct_timing_print_all();
  oct_timing_clear ();
  printf("\n");
  oct_mmalloc_print(oct_mmalloc_get_current());
  printf("\ntotal test duration: "); oct_chrono_stop(&chr);
  oct_chrono_print(&chr); printf("\n\n");  
  return 0;
}
