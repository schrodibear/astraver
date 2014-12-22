#define rcu_head callback_head

typedef unsigned int uint32_t;

typedef struct {
  int dummy;
} PDP_ROLE_T;

typedef struct {
 int counter;
} atomic_t;

typedef unsigned gfp_t;

struct callback_head {
 struct callback_head *next;
 void (*func)(struct callback_head *head);
};

typedef struct PDP_ROLES_T /*  role label for subjects and objects*/
{
    PDP_ROLE_T*     roles;
    uint32_t        roles_cnt;

    PDP_ROLE_T*     aroles;
    uint32_t        aroles_cnt;

    atomic_t        ucnt;
    struct rcu_head rcu;

} PDP_LROLES_T;

typedef struct PDP_ROLES_T     PDPR_T;

/*@ assigns \result;
    allocates \result;
    ensures \fresh(\result, 1) && \offset_min(\result) == 0 && \valid(\result) && \fresh(&\result->ucnt, 1);
*/
PDPR_T* pdpr_get_new(gfp_t f)
{
  PDPR_T *result = malloc(sizeof (PDPR_T));
  if (result->ucnt.counter < 10)
    result->ucnt.counter++;

  return result;
}


/*@ assigns \nothing;
    allocates \nothing;
 */
int main(void)
{
  PDPR_T* r = pdpr_get_new(0);
  free(r);
}
