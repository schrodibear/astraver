#ifndef SPEC_LIB_H
#define SPEC_LIB_H

#ifdef SPECIFICATION

//@ ghost enum status {SUCCESS, FAILURE};


/*@ requires \valid(fmt);
    assigns \nothing;
    ensures 0 <= \result;
   */
extern int printk(const char *fmt, ...);

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == \old(v->counter) - 1;
    behavior TRUE:
        assumes v->counter == 0;
        ensures \result == 1;
    behavior FALSE:
        assumes v->counter != 0;
        ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
  */
extern /*static inline*/ int atomic_dec_and_test(atomic_t *v);

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == \old(v->counter) - 1;
  */
extern /*static inline*/ void atomic_dec(atomic_t *v);

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == \old(v->counter) + 1;
  */
extern /*static inline*/ void atomic_inc(atomic_t *v);

/*@ requires \valid(v);
    assigns \nothing;
    ensures \result == v->counter;
  */
extern /*static inline*/ int atomic_read(const atomic_t *v);

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == i;
 */
extern /*static inline*/ void atomic_set(atomic_t *v, int i);


/*@ axiomatic MemSet {
    logic 𝔹 memset{L}(char *s, ℤ c, ℤ n);
    // reads s[0..n - 1];
    // Returns [true] iff array [s] contains only character [c]

    axiom memset_def{L}:
      \forall char *s; \forall ℤ c; \forall ℤ n;
         memset(s,c,n) <==> \forall ℤ i; 0 <= i < n ==> s[i] == c;
    }
  */
/*@ requires \valid(((char*)s)+(0..count - 1));
    assigns ((char*)s)[0..count - 1] \from c;
    assigns \result \from s;
    ensures memset((char*)s,c,count);
    ensures \result == s;
  */
void *memset(void *s, int c, size_t count);

/*@ assigns \result \from size;
    ensures \result == \null ||
            // UNSUPPORTED: \block_length(\result) == size &&
            \valid((char *)\result+(0..size));
 */
extern /*static inline*/ void *kmalloc(size_t size, gfp_t flags);

/*@ assigns \result \from size;
    ensures \result == \null ||
               // UNSUPPORTED: \block_length(\result) == size &&
               \valid((char *)\result+(0..size)) &&
               memset((char *)\result, 0, size);
 */
extern /*static inline*/ void *kzalloc(size_t size, gfp_t flags);

#endif /* SPECIFICATION */
#endif /* SPEC_LIB_H    */
