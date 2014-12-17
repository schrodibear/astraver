
typedef enum {N, A, B} trans_t;

/*@ behavior more_than_five:
      assumes x > 5;
      ensures x > 5 <==> \result == A;

    behavior less_than_five:
      assumes x >= 0 && x <= 5;
      ensures (x >= 0 && x <= 5) <==> \result == B;

    behavior none:
      assumes x < 0;
      ensures x < 0 <==> \result == N;

   complete behaviors;
   disjoint behaviors;
 */
trans_t compute_trans(int x)
{
  if (x > 5)
    return A;
  else if (x >= 0)
    return B;
  else
    return N;
}

/*@ behavior more_than_five:
      assumes x > 5;
      ensures x > 5 ==> \result == A;

    behavior less_than_five:
      assumes x >= 0 && x <= 5;
      ensures (x >= 0 && x <= 5) ==> \result == B;

    behavior none:
      assumes x < 0;
      ensures x < 0 ==> \result == N;

   complete behaviors;
   disjoint behaviors;
 */
trans_t compute_trans2(int x)
{
  if (x > 5)
    return A;
  else if (x >= 0)
    return B;
  else
    return N;
}

/*@ ensures \result == -1 || \result == 1 || \result == 2;
 */
int main(int x)
{
  trans_t trans = N;

  trans = compute_trans(x);

  switch(trans) {
  case N:
    //@ assert 1==2;
    return -1;
    break;

  case A:
    return 1;
    break;

  case B:
    return 2;
    break;

  default:
    return -1;
    break;
  }
}
