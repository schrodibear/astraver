
// Dummy specification
//@ assigns \nothing;
void *malloc(unsigned long size);

/*@ axiomatic casts {
  @   predicate int8_as_int32(int a, char d0, char d1, char d2, char d3);
  @ }
  @*/

/*@ axiomatic validity {
  @   predicate strict_valid_char(char *p, integer l, integer r) = \offset_min(p) == l && \offset_max(p) == r;
  @ }
  @
 */

/*@ requires \typeof(data) <: \type(char *) && strict_valid_char((char *)data, 0, 3);
  @ assigns *((char *)data+(0..3));
  @ allocates \nothing;
  @ ensures \let pc = (char *) data; int8_as_int32((int) 0, pc[0], pc[1], pc[2], pc[3]);
 */
void f(void *data)
{
        //@ jessie pragma ((char *) data) :> int *;
        ((int *) data)[0] = 0;
        //@ jessie pragma ((int *) data) :>  char *;
}

/*@ allocates \nothing;
  @ assigns \nothing;
 */
void caller()
{
        char *p;

        p = malloc(sizeof(char) * sizeof(int) * 1);

        f(p);

        //@ assert  \typeof(p) <: \type(char *);

        //@ assert p[0] == p[1] == p[2] == p[3] == 0;
        free(p);
}

