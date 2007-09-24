package java.lang;

public static final class Math {

    
    public static /*@ pure @*/ int abs_int(int n) {}

    //@ public normal_behavior
    public static /*@ pure @*/ double sqrt(double x) {}

    //@ public normal_behavior
    public static /*@ pure @*/ double abs(double n) {}

    //@ public normal_behavior
    public static /*@ pure @*/ double asin(double x) {}

    //@ public normal_behavior
    public static /*@ pure @*/ double min(double x, double y) {}

    //@ public normal_behavior
    public static /*@ pure @*/ double max(double x, double y) {}

    public static final float PI = 3.14;

    //@ public normal_behavior
    public static /*@ pure */ double atan2(double x, double y) {}

}
