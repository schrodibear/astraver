/*@ requires (\typeof(p) <: \type(char *) ==> \valid((const char *)p)) && \valid(s) && flag1 == flag2 == 0;
  @  ensures \result == 0;
  @
 */
extern int dummy_callback1(int flag1, int flag2, void *p, const char *s);

/*@ requires (\typeof(p) <: \type(char *) ==> \valid((const char *)p)) && \valid(s) && flag1 == flag2 == 0;
  @  ensures \result == 0;
  @
 */
extern int dummy_callback2(int flag1, int flag2, void *p, const char *s);

/*@ ensures \result == 0;
 */
extern int dummy_callback3();

typedef int (*callback_t) (int, int, void *, const char *);

struct callbacks {
  callback_t cb1;
  int (*cb2) (void);
};

struct outer {
    struct callbacks *cbs;
};

/*@ requires \valid(pouter) && \valid(pouter->cbs);
  @ requires pouter->cbs->cb1 == &dummy_callback1 || pouter->cbs->cb1 == &dummy_callback2;
  @ requires pouter->cbs->cb2 == (int (*)(void))&dummy_callback3;
  @ ensures \result == 0;
*/
int caller (struct outer *pouter)
{
  char *s = "const char ";
  return pouter->cbs->cb1(0, 0, s, "const char") || pouter->cbs->cb2();
}