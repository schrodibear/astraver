/*@ logic integer value{L}(Counter c) = 
  @    \at(c.increments,L) - \at(c.decrements,L);
  @*/

public class Counter {
    private int increments;
    private int decrements;


    //@ ensures value{Here}(this) == value{Old}(this) + 1;
    public void increment() {
        increments++;
    }

    //@ ensures value{Here}(this) == value{Old}(this) - 1;
    public void decrement() {
        decrements++;
    }

}

