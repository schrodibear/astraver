#include <stdlib.h>
#include <string.h>

typedef unsigned long ulong;

/*@ axiomatic casts {
  @    predicate int8_as_int32(int a, char d0, char d1, char d2, char d3);
  @    predicate int32_as_int8(int a, char d0, char d1, char d2, char d3);
  @    predicate int8_as_uint32(unsigned long a, char d0, char d1, char d2, char d3);
  @    predicate uint32_as_int32(int b, unsigned long a);
  @ }
  @*/

/*@ axiomatic validity {
  @   predicate strict_valid_char(char *p, integer l, integer r) = \offset_min(p) == l && \offset_max(p) == r;
  @   predicate strict_valid_int(int *p, integer l, integer r) = \offset_min(p) == l && \offset_max(p) == r;
  @   predicate strict_valid_ulong(unsigned long *p, integer l, integer r) = \offset_min(p) == l && \offset_max(p) == r;
  @   predicate allocable_block{L}(void *q) =
  @     \forall void *p;
  @          (p == q || p != q) &&
  @          \base_addr(p) == \base_addr(q) ==>
  @             \offset_min(p) == 0 - (p - q) &&
  @             \offset_max(p) == -1 - (p - q);
  @
  @ }
  @*/

// Dummy specification
//@ assigns \nothing;
void *memset(void *c, int v, size_t n);

/*@ allocates \result;
  @ assigns \nothing;
  @ ensures \offset_min(\result) == 0 && \offset_max(\result) == 23;
  @ ensures \fresh(\result, 24);
  @ ensures *\result == *(\result + 12) == c;
  @ ensures \let c = \result; int8_as_int32(d, c[4], c[5], c[6], c[7]) &&
  @                           int8_as_int32(d, c[16], c[17], c[18], c[19]);
  @ ensures \let c = \result; int8_as_uint32(f, c[8], c[9], c[10], c[11]) &&
  @                           int8_as_uint32(f, c[20], c[21], c[22], c[23]);
  @*/
char *init_buffer(char c, int d, unsigned long f)
{
        char *buf = malloc (6 * sizeof(int));

        memset(buf, 0, 6 * sizeof(unsigned long));
        *buf = c;
        buf[3 * sizeof(unsigned long)] = c;

        //@ ghost L1:
        //@ jessie pragma buf :> int *;
        //@ assert \let q = (int *)buf; allocable_block{Pre}(q);
        //@ assert strict_valid_int((int *)buf, 0, 5);

        //@ assert int8_as_int32(*(int *)buf, c, (char) 0, (char)0, (char) 0);
        //@ assert int8_as_int32(((int *)buf)[3], c, (char) 0, (char) 0, (char) 0);

        //@ assert (int *)(buf + sizeof(unsigned long)) == &((int*)buf)[1];

        *(int *)(buf + sizeof(unsigned long)) = ((int *)buf)[4] = d;

        //@ ghost L6:
        //@ jessie pragma ((int *) buf) :> unsigned long *;
        //@ assert \let q = (int *)buf; allocable_block{Here}(q);
        // Dirty temporary fix
        //@ ghost void * buf_0 = buf;
        //@ assert strict_valid_ulong((unsigned long *)buf_0, 0, 5);

        //@ assert (unsigned long *)(&buf[8]) == &((unsigned long *)buf)[2];
        *(unsigned long *)(buf + 2 * sizeof(unsigned long)) = f;
        ((unsigned long *)buf)[5] = f;

        //@ ghost L:
        //@ jessie pragma ((unsigned long *) buf) :> char *;
        //@ ghost void * pp = (unsigned long *) buf;
        //@ assert strict_valid_char(buf, 0, 23);

        /*@ assert \forall void *p;
          @        (p == buf || p != buf) &&
          @        \base_addr(p) !=  \base_addr((unsigned long *) buf) &&
          @        \base_addr(p) != \base_addr((int *)buf)  &&
          @        \base_addr(p) != \base_addr(buf) ==>
          @        \at(\offset_min(p), Pre) == \at(\offset_min(p), Here) &&
          @        \at(\offset_max(p), Pre) == \at(\offset_max(p), Here);
          @
          @*/
        //@ assert \let q = (int *)buf; allocable_block{Here}(q);
        //@ assert \let q = (unsigned long *)buf; allocable_block{Here}(q);

        return buf;
}

/*@ requires \valid(buf);
  @ ensures \result == *buf;
  @*/
char get_char(char *buf)
{
        return *(char *)buf;
}

/*@ requires strict_valid_char(buf, 0, 23);
  @ allocates \nothing;
  @ assigns \nothing;
  @ ensures int8_as_int32(\result, buf[4], buf[5], buf[6], buf[7]);
  @*/
int get_int(char *buf)
{
        //@ jessie pragma buf :> int *;
        int result = ((int *) buf)[1];
        //@ jessie pragma ((int *) buf) :> char *;
        return result;
}

/*@ requires \valid(&((int *)buf)[1]) && \typeof(buf) <: \type(int *);
  @ assigns \nothing;
  @ ensures \result == ((int *)buf)[1];
  @*/
int get_int2(void *buf)
{
        return ((int *)buf)[1];
}

/*@ requires \valid(buf+1);
  @ assigns \nothing;
  @ ensures \result == buf[1];
  @*/
int get_int3(int *buf)
{
        return buf[1];
}

/*@ requires strict_valid_char(buf, 0, 23);
  @ allocates \nothing;
  @ assigns \nothing;
  @ ensures int8_as_uint32(\result, buf[8], buf[9], buf[10], buf[11]);
  @*/
ulong get_ulong(char *buf)
{
        //@ jessie pragma buf :> ulong *;
        ulong result = *(unsigned long *)(buf + 2 * sizeof (int));
        //@ jessie pragma ((ulong *) buf) :> char *;
        return result;
}

/* requires \valid((char *)buf+(0..23)) && \typeof(buf) <: \type(char *);
  @ allocates \nothing;
  @ assigns (int *)((char *)buf+(0..-1));
  @ ensures \result == ((int *)buf)[3];
  @*/
/*
int get_int_and_reinterpret(void *buf)
{
        //@ jessie pragma ((char *) buf) :> int *;
        return ((int *) buf)[3];
}
*/

/*@ requires \valid(buf);
  @ assigns *buf;
  @ ensures *buf == c;
  @*/
void set_char(char *buf, char c)
{
        *buf = c;
}

/*@ requires strict_valid_char(buf, 0, 23);
  @ allocates \nothing;
  @ assigns *(buf+(4..7));
  @ ensures int8_as_int32(a, buf[4], buf[5], buf[6], buf[7]);
  @*/
void set_int(char *buf, int a)
{
        //@ jessie pragma buf :> int *;
        //@ assert (int *)(buf + sizeof (int)) == &((int *)buf)[1];
        *(int *)((char *)buf + sizeof(int)) = a;
        //@ jessie pragma ((int *) buf) :> char *;
}

/*@ requires \valid(&((int *)buf)[1]) && \typeof(buf) <: \type(int *);
  @ assigns ((int *)buf)[1];
  @ ensures ((int *)buf)[1] == a;
  @*/
void set_int2(void *buf, int a)
{
        ((int *)buf)[1] = a;
}

/*@ requires \valid(&buf[1]);
  @ assigns buf[1];
  @ ensures buf[1] == a;
  @*/
void set_int3(int *buf, int a)
{
        buf[1] = a;
}

/* requires \valid((int *)buf+(0..5)) && \typeof(buf) <: \type(int *);
  @ allocates \nothing;
  @ assigns (char *)((int *)buf);
  @ ensures *(char *)buf == c;
  @*/
/*
void set_char_and_reinterpret(void *buf, char c)
{
        //@ jessie pragma ((int *) buf) :> char *;
       *(char *)buf = c;
}
*/

void *buf;

/*@ allocates buf;
  @ assigns buf;
  @ ensures \typeof(buf) <: \type(char *) && \offset_min(buf) == 0 && \offset_max(buf) == 23;
  @ ensures \fresh(buf, 24);
  @ ensures *(char *)buf == *((char *)buf + 12) == c;
  @ ensures \let c = (char*) buf; int8_as_int32(d, c[4], c[5], c[6], c[7]) &&
  @                               int8_as_int32(d, c[16], c[17], c[18], c[19]);
  @ ensures \let c = (char*) buf; int8_as_uint32(f, c[8], c[9], c[10], c[11]) &&
  @                               int8_as_uint32(f, c[20], c[21], c[22], c[23]);
  @*/
void store_in_buf(char c, int d, unsigned long f)
{
        buf = init_buffer (c, d, f);
}

/*@ assigns buf;
  @ allocates \nothing;
 */
void test(void)
{
        char c;
        int d;
        unsigned long f;
        //@ ghost L:
        store_in_buf(c, d, f);
        set_int(buf, -98);
        c = get_char(buf);
        d = get_int(buf);
        f = get_ulong(buf);
        //@ assert c == \at(c, L);
        //@ assert d == -98;
        //@ assert f == \at(f, L);
        free(buf);
        /*@ assert \forall void *p;
          @    (p == buf || p != buf) &&
          @    \base_addr(p) == \base_addr(buf) ==>
          @    \at(\offset_min(p), Here) == \at(\offset_min(p), Pre) == 0 - (p - buf) &&
          @    \at(\offset_max(p), Here) == \at(\offset_max(p), Pre) == -1 - (p - buf);
          @*/
}


/* requires \offset_min(buf) == -1 && \offset_max(buf) == 0;
  @ assigns \nothing;
  @ allocates buf;
  @ ensures \valid((char*)buf) && \offset_min(buf) == 0;
  @*/
/*
void test2(void)
{
        char c;
        int d, d2, d3;
        unsigned long f;
        //@ ghost L:
        store_in_buf(c, -99, f);
        //d = get_int_and_reinterpret(buf);
        d2 = get_int2(buf);
        d3 = get_int3(buf);
        if (c)
          set_int2(buf, -98);
        else
          set_int3(buf, -98);
        //set_char_and_reinterpret(buf, 'c');
        c = get_char(buf);
        d = get_int(buf);
        f = get_ulong(buf);
        //@ assert c == 'c';
        //@ assert d == -98;
        //@ assert d2 == d3 == -99;
        //@ assert f == \at(f, L);

        set_int4(&d3, 1);
        //d2 = get_int4(&d3);
        //@ assert d2 == 1;
}
*/

/*@ requires \offset_min(buf) == 0 && \valid((char *)buf) && \typeof(buf) <: \type(char *);
  @ frees buf;
  @ ensures \offset_min(buf) == 0 && \offset_max(buf) == -1;
  @*/
void test3(void)
{
        free(buf);
}
