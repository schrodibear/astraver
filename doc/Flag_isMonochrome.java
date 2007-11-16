/*@ public normal_behavior
  @  requires 0 <= i && i <= j && j <= t.length;
  @  ensures \result <==> (\forall integer k; i <= k && k < j ==> t[k] == c);
  @*/
public /*@ pure @*/ boolean isMonochrome(int i, int j, int c);
