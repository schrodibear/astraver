/* oct_polka.c
   Interface with NewPolka polyhedra library.
   
   This file is part of the Octagon Abstract Domain Library.
   Please read the COPYING file packaged in the distribution.
   Main web page is: http://www.di.ens.fr/~mine/oct/

   Copyright (C) Antoine Mine' 2000-2002
 */

#include <oct.h>
#include <oct_private.h>

#ifdef OCT_HAS_NEW_POLKA

/****************************/
/* Interface with New Polka */
/****************************/

/* Convert an octagon into a polyhedron.
   Add the matsize(m->n) constraints of the octagon, except constraints
   of the form x_i-x_j <= +oo, or x_i-x_i <= 0, with poly_add_contraints.
   Instead of adding the constraints one-per-one (too many calls to
   poly_add_constraints), or adding all constraints at once (N^3 memory cost
   because we can add many redundant constraints), add the constraints per
   chunk of MATBUF constraints.
*/
poly_t*
OCT_PROTO(to_poly) (oct_t* m)
{
  poly_t* r;
  OCT_ENTER("oct_to_poly",0);
  if (m->state==OCT_EMPTY) r = poly_empty (m->n);
  else {
    /* I'm not sure what I'm doing, so I use poly_universe and
       poly_add_constraints instead of poly_of_constraints 
    */
    const size_t n2 = m->n*2;
    var_t i,j;
    num_t* c = m->c;
    poly_t* rr;
    /* constraints from an octagon are passed to the poly by chunks of this
       size, to avoid too many calls to poly_add_constraints, ... */
    static const int MATBUF = 50;
    matrix_t* mat = matrix_alloc (MATBUF, m->n+polka_dec, false);
    matrix_clear (mat);
    mat->nbrows = 0;
    r = poly_universe (m->n);
    for (i=0;i<n2;i++) {
      const var_t ii = i|1;
      for (j=0;j<=ii;j++,c++)
	if (num_fits_frac(c) && i!=j) {
	  long ai = (i&1)?-1:1;
	  long aj = (j&1)?1:-1;
	  if (mat->nbrows==MATBUF) {
	   rr = poly_add_constraints (r,mat);
	   poly_free (r);
	   r = rr;
	   matrix_clear (mat);
	   mat->nbrows = 0;
	  }
	  pkint_set_si(mat->p[mat->nbrows][0],num_get_den(c));
	  pkint_set_si(mat->p[mat->nbrows][1],num_get_num(c));
	  if (i==(j^1)) {
	    pkint_set_si(mat->p[mat->nbrows][polka_dec+i/2],
			 ((i&1)?-1:1)*num_get_den(c));
	    pkint_add(mat->p[mat->nbrows][polka_dec+i/2],
		      mat->p[mat->nbrows][polka_dec+i/2],
		      mat->p[mat->nbrows][polka_dec+i/2]);
	  }
	  else {
	    pkint_set_si(mat->p[mat->nbrows][polka_dec+i/2],
			 ((i&1)?-1:1)*num_get_den(c));
	    pkint_set_si(mat->p[mat->nbrows][polka_dec+j/2],
			 ((j&1)?1:-1)*num_get_den(c));
	  }
	  mat->nbrows++;
	}
    }
    rr = poly_add_constraints (r,mat);
    poly_free (r);
    r = rr;
    matrix_free (mat);
  }
  OCT_EXIT("oct_to_poly",0);
  return r;
}



/* Use the frame representation of the polyhedron.
   For each octagon constraint, x_i-x_j <= c, find the smallest c such that
   all elements of the frame are satisfied by the constraint.
 */
oct_t*
OCT_PROTO(from_poly) (poly_t* p)
{
  oct_t* r;
  long* buf;
  const var_t n = poly_dimension (p);
  const var_t n2 = n*2;
  var_t k;
  bool first;
  num_t w;

  OCT_ENTER("oct_from_poly",1);

  OCT_ENTER("[poly_minimize]",2);
  poly_minimize(p);
  OCT_EXIT("[poly_minimize]",2);
  if (poly_is_empty(p)) { r = oct_empty (n); goto end; }

  r = oct_universe (n);
  buf = new_n(long,n2);
  num_init(&w);

  /* vertices */
  first = true;
  for (k=0;k<p->F->nbrows;k++) {
    var_t  i,j;
    num_t* c = r->c;
    pkint_t* m = p->F->p[k];
    long m0 = pkint_get_si(m[0]);
    long m1 = pkint_get_si(m[1]);
    if (m0 && m1) {
      m += polka_dec;
      for (i=0;i<n2;i+=2,m++) {
	buf[i  ] = pkint_get_si(*m);
	buf[i+1] = -buf[i];
      }
      if (first) {
	first = false;
	for (i=0;i<n2;i++) {
	  const var_t ii = i|1;
	  for (j=0;j<=ii;j++,c++)
	    if (i!=j)
	      num_set_frac(c,buf[j]-buf[i],m1);
	}
      }
      else {
	for (i=0;i<n2;i++) {
	  const var_t ii = i|1;
	  for (j=0;j<=ii;j++,c++)
	    if (i!=j) {
	      num_set_frac(&w,buf[j]-buf[i],m1);
	      num_max(c,c,&w);
	    }
	}
      }
    }
  }

  /* lines & rays */
  for (k=0;k<p->F->nbrows;k++) {
    var_t  i,j;
    num_t* c = r->c;
    pkint_t* m = p->F->p[k];
    long m0 = pkint_get_si(m[0]);
    long m1 = pkint_get_si(m[1]);
    if (!m0 || !m1) {
      m += polka_dec;
      for (i=0;i<n2;i+=2,m++) {
	buf[i  ] = pkint_get_si(*m);
	buf[i+1] = -buf[i];
      }
      if (!m0) { /* line */
	for (i=0;i<n2;i++) {
	  const var_t ii = i|1;
	  for (j=0;j<=ii;j++,c++)
	    if (buf[j]-buf[i]) num_set_infty(c);
	}
      }
      else { /* ray */
	for (i=0;i<n2;i++) {
	  const var_t ii = i|1;
	  for (j=0;j<=ii;j++,c++)
	    if (buf[j]-buf[i]>0) num_set_infty(c);
	}
      }
    }
  }
  oct_mm_free (buf);
  num_clear(&w);
  r->state = OCT_NORMAL;
 end:
  OCT_EXIT("oct_from_poly",1);
  return r;
}

#endif
