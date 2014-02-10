#define BOUND 0x1p-20

struct
{
  float x1;
} M;

struct
{
  float M1;
} L;

/*@ requires \abs(L.M1) <= BOUND;*/
void Test(void)
{
  float result;
  //@ assert \abs(L.M1) <= BOUND;

  M.x1 = L.M1 / 3600.0;
  //@ ghost float tmp1 = L.M1 / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert \abs(M.x1) <= BOUND;

  result = M.x1 * 100.0;
  //@ ghost float tmp2 = tmp1 * 100.0;
  //@ assert \abs(tmp2) <= BOUND;
  //@ assert \abs(result) <= BOUND;
}
