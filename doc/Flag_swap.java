/*@ public normal_behavior
  @  requires   0 <= i && i < t.length && 0 <= j && j < t.length;
  @  modifiable t[i],t[j];
  @  ensures    t[i] == \old(t[j]) && t[j] == \old(t[i]);
  @*/
public void swap(int i, int j);
