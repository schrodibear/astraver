
typedef unsigned int T_WORD32;

typedef struct {
  T_WORD32 a;
  T_WORD32 b;
  T_WORD32 c;
}T_STRUCT;

T_STRUCT struc;


/*@ assigns struc;
  @ ensures struc == \old(struc);
  @*/

void test (T_STRUCT b)
{
  if (struc.b>0)
    struc=b;
}
