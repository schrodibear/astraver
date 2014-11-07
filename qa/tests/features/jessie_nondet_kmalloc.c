/*@ assigns \nothing; */
extern void *kmalloc(unsigned long size, int flags);

/*@ assigns \nothing; */
extern void memcpy(void *dst, const void *src, unsigned long n);
/*@ assigns \nothing; */
extern void memset(void *dst, int value, unsigned long n);
/*@ assigns \nothing; */
extern int memcmp(void *p1, void *p2, unsigned long n);

char fstr[] = /*@ fstr_literal = */ "String constant";

//@ ghost int initialized = 0;

/*@ global invariant fstr_init:
  @        ! initialized ==> \forall integer i; \valid(&fstr[i]) ==> fstr[i] == fstr_literal[i];
*/

/*@ axiomatic allocation_footprint {
  @    predicate not_allocates{L1, L2}(void *p) =
  @      \at(\offset_min(p), L1) == \at(\offset_min(p), L2) &&
  @      \at(\offset_max(p), L1) == \at(\offset_max(p), L2);
  @  }
  @
 */

/*@ requires ! initialized;
  @ assigns initialized, fstr[6];
  @ ensures initialized &&
  @           (\forall integer i; \valid(&fstr[i]) && i != 6 ==> fstr[i] == fstr_literal[i]) &&
  @           fstr[6] == '_';
  */
void initialize_fstr()
{
  fstr[6] = '_';
  //@ ghost initialized = 1;
}

//@ ghost enum outcome {SUCCESS, FAILURE1, FAILURE2, FAILURE3};
//@ ghost static enum outcome outcome;

//@ ghost char **f_alloc1;
//@ ghost char *f_alloc2, *f_alloc3;

/*@ requires initialized;
  @ assigns outcome, f_alloc1, f_alloc2, f_alloc3;
  @ allocates f_alloc1, f_alloc2, f_alloc3;
  @ behavior success:
  @   ensures outcome == SUCCESS ==>
  @            \valid(\result+(0..1)) &&
  @            \valid(\result[0]+(0..3)) &&
  @            \valid(\result[1]+(0..sizeof(fstr) - 1)) &&
  @            (\forall integer i; 0 <= i <= 2 ==> \result[0][i] == 'A') &&
  @            \result[0][3] == '\000' &&
  @            (\forall integer i; 0 <= i < sizeof(fstr) ==> \result[1][i] == fstr[i]);
  @ behavior failure:
  @   ensures outcome == FAILURE1 || outcome == FAILURE2 || outcome == FAILURE3 ==>
  @             \result == 0 &&
  @             not_allocates{Pre, Post}(f_alloc1) && not_allocates{Pre, Post}(f_alloc2) && not_allocates{Pre, Post}(f_alloc3);
  @ complete behaviors;
 */
char **f()
{
  char **str_list = kmalloc(2 * sizeof(char *), 0);
  //@ ghost f_alloc1 = str_list;
  if (str_list) {
    str_list[0] = kmalloc(5 * sizeof(char), 0);
    //@ ghost f_alloc2 = str_list[0];
    if (str_list[0]) {
      memcpy(str_list[0], /*@ aaau_literal = */ "AAAU", 5);
      memset(&str_list[0][3], 0, 1);
      //@ assert str_list[0][3] == 0;
    } else {
      free(str_list);
      //@ ghost outcome = FAILURE2;
      return 0;
    }
    str_list[1] = kmalloc(sizeof(fstr), 0);
    //@ ghost f_alloc3 = str_list[1];
    if (str_list[1]) {
      //@ assert str_list[0][3] == 0;
      //@ assert str_list[0][0] == 'A' && str_list[0][1] == 'A' && str_list[0][2] == 'A';
      memcpy(str_list[1], fstr, sizeof(fstr));
      //@ assert str_list[0][3] == 0;
      //@ assert str_list[0][0] == 'A' && str_list[0][1] == 'A' && str_list[0][2] == 'A';
      //@ ghost outcome = SUCCESS;
      return str_list;
    } else {
      free(str_list[0]);
      free(str_list);
      //@ ghost outcome = FAILURE3;
      return 0;
    }
  } else {
    //@ ghost outcome = FAILURE1;
    return 0;
  }
}

/*@ requires ! initialized;
  @ ensures \result == 1 || \result == 0;
  */
int main(void)
{
  char **result;
  int result1, result2;

  //@ assert ! initialized;

  initialize_fstr();
  result = f();

  if (result) {
    result1 = memcmp(result[0], /*@ aaa_literal = */"AAA", 4);
    //@ assert result1 == 0;
    result2 = memcmp(result[1], /*@ string_constant_literal = */"String_constant", 16);
    //@ assert result2 == 0;
    return result1 | result2;
  } else {
    return 1;
  }
}
