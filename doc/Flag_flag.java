/*@ public normal_behavior
  @  ensures 
  @   (\exists int b,r; isMonochrome(0,b,BLUE) && 
  @    isMonochrome(b,r,WHITE) && isMonochrome(r,t.length,RED));
  @*/
public void flag()

