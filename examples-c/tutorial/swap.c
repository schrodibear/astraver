/*@ requires \valid_index(t,i) && \valid_index(t,j) 
  @*/
void swap(int t[],int i,int j) {
  int tmp = t[i];
  t[j] = t[i]; 
  t[i] = tmp;
}


