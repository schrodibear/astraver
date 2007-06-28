
//@ logic int num_of_pos(int i,int j,int t[]) reads t[i]

/*@ axiom num_of_pos_empty :
  @   \forall int i, int j, int t[];
  @       i > j => num_of_pos(i,j,t) == 0
  @*/
 
/*@ axiom num_of_pos_true_case :
  @   \forall int i, int j, int k, int t[];
  @       i <= j && t[j] > 0 => 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1
  @*/

/*@ axiom num_of_pos_false_case :
  @   \forall int i, int j, int k, int t[];
  @       i <= j && ! (t[j] > 0) => 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t)
  @*/

/*@ axiom num_of_pos_strictly_increasing:
  @   \forall int i, int j, int k, int l, int t[];
  @       j < k && k <= l && t[k] > 0 => num_of_pos(i,j,t) < num_of_pos(i,l,t)
  @*/

/*@ requires length >= 0 && \valid_range(t,0,length-1)
  @*/
void m(int t[], int length) {
  int count = 0;
  int i;
  int *u;

  /*@ invariant
    @    0 <= i && i <= length && 
    @    0 <= count && count <= i && 
    @    count == num_of_pos(0,i-1,t)  
    @ variant length - i
    @*/
  for (i=0 ; i < length; i++) {
    if (t[i] > 0) count++;
  }
  u = (int *)calloc(count,sizeof(int));
  count = 0;
  
  /*@ invariant
    @    0 <= i && i <= length && 
    @    0 <= count && count <= i && 
    @    count == num_of_pos(0,i-1,t)
    @ variant length - i
    @*/
  for (i=0 ; i < length; i++) {
    if (t[i] > 0) {
      u[count++] = t[i];
    }
  }
}

