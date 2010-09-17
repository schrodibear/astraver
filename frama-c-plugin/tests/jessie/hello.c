/*@ ensures \result == ((i < j) ? j : i);
  @*/
int max(int i, int j) {
        return (i < j) ? j : i;
}

