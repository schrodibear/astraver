
public class Flag {

  public static final int BLUE = 1, WHITE = 2, RED = 3;

    //@ public normal_behavior
    //@   ensures \result <==> (i == BLUE || i == WHITE || i == RED);
    public static /*@ pure @*/ boolean isColor(int i);

