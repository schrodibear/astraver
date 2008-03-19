
//@ type larray

/* [create(x)] returns an array  
 * where each cell contains [x] 
 **/
//@ logic larray create(double x);

//@ logic double select(larray t, integer i);

/*@ logic larray 
  @  store(larray t, integer i, double x);
  @*/

/*@ axiom select_store_eq:
  @  \forall larray t, integer i, double x;
  @   select(store(t,i,x),i) == x;
  @*/

/*@ axiom select_store_neq:
  @  \forall larray t, integer i, integer j;
  @   \forall double x;
  @    i != j ==> 
  @     select(store(t,i,x),j) == select(x,j);
  @*/


interface PArrayInterface {

    //@ model larray model_array;
    //@ model integer model_length;
  
    /*@ requires n >= 0;
      @ ensures \result.model_array == create(0.0);
      @ ensures \result.model_length == n;
      @*/
    static PArrayInterface create(int n);
    
    /*@ requires 0 <= i < this.model_length;
      @ assigns \nothing;
      @ ensures \result == select(this.model_array,i);
      @*/
    double get(int i);

    /*@ requires 0 <= i < this.model_length;
      @ assigns \nothing;
      @ ensures \fresh(\result); 
      @ ensures \result.model_array == store(this.model_array,i,x);
      @ ensures \result.model_length == this.model_length;
      @*/
    PArrayInterface set(int i, double x);

}


abstract class Data {

    abstract double get(int i);
    
    abstract PArray set(int i, double x, PArray parent);

}

class Arr extends Data {

    double table[];

    //@ invariant table != null;
    /*@ invariant model_length == table.length &&
      @   \forall integer i; 
      @     0 <= i < table.length ==> table[i] == get(model_array,i);
      @*/

    Arr(int n) {
	table = new double[n];
    }

    double get(int i) {
	return table[i];
    }

    PArray set(int i, double x, PArray parent) {
	double old = table[i];
	table[i] = x;
	PArray tmp1 = new PArray(this);
	Data tmp2 = new Diff(i,old,tmp1);
	parent.contents = tmp2;
	return tmp1;
    }

    String toString() {
	String s = "Arr [";
	for (int i = 0; i < table.length; i++)
	    s += i + "; ";
	return (s + "]");
    }
}

class Diff extends Data {

    private int index;
    private double value;
    private PArray remaining;

    //@ invariant remaining != null;
    //@ invariant repr(model_length.store(index,value,remaining.model_array),this)

    Diff(int i, double x, PArray rem) {
	index = i;
	value = x;
	remaining = rem;
    }

    double get(int i) {
	if (i == index) return value;
	return remaining.get(i);
    }

    PArray set(int i, double x, PArray t) {
	Data tmp = new Diff(i,x,t);
	return new PArray(tmp);
    }

    String toString() {
	return "Diff " + index + ", " + value + ", " + remaining;
    }
}

public class PArray implements PArrayInterface 
{
    
    private Data contents;
    
    //@ invariant contents != null;
    //@ invariant repr(model_length,model_array,contents);
    
    PArray(Data d) {
	contents = d;
    }
    
    static PArray create(int n) {
	return new PArray(new Arr(n));
    }
    
    double get(int i) {
	return contents.get(i);
    }

    PArray set(int i, double x) {
	return contents.set(i,x,this);
    }

    String toString() {
	return ("-> " + contents);
    }

    public static void main(String argv[]) {

	PArray t1 = PArray.create(4);
	PArray t2 = t1.set(0,2.2);
	PArray t3 = t2.set(1,3.3);
	System.out.println("t1 = " + t1);
	System.out.println("t2 = " + t2);
	System.out.println("t3 = " + t3);
    }

}






	
	
	
