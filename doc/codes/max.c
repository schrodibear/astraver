//@ ensures \result == \max(i,j);
int max(int i, int j) {
  return (i < j) ? j : i;
}
