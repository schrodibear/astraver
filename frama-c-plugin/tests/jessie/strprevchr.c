/*@
  @ predicate AbsentTail{L1,L2}(int e1, int e2, char c, char *array) =
  @    \forall int i;
  @       e2+1 <= i && i <= e1
  @         ==> \at(array[i],L1) != c;
  @*/

/*@ requires endi >= 0 && \valid_range(array, 0, endi);
  @ assigns \nothing;
  @ behavior absent:
  @   assumes \forall int i; 0 <= i <= endi ==> array[i] != c;
  @   ensures \result == -1;
  @ behavior present:
  @   assumes \exists int i; 0 <= i <= endi ==> array[i] == c;
  @   ensures 0 <= \result <= \at(endi, Pre);
  @*/
int strprevchr(int endi, char c, const char array[]) {
  /*@
    @ loop invariant \at(endi,Pre) >= endi >= -1 && AbsentTail{Pre,Here}(\at(endi,Pre), \at(endi,Here), c, array);
    @ loop variant endi;
    @*/
  while (endi >= 0 && array[endi] != c)
    endi--;
  return endi;
}


