
/* JLS 2.0, page 216 */

class Point { int x,y; }

class ColoredPoint extends Point { int color; }

class Test {
    public static void main(String[] args) {
	ColoredPoint[] cpa = new ColoredPoint[10];
	Point[] pa = cpa;
	System.out.println(pa[1] == null);
	try {
	    pa[0] = new Point();
	}
	catch (ArrayStoreException e) {
	    System.out.println(""+e);
	}
    }
}
