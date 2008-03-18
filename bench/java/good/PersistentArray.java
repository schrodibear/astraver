

//@ type logic_tab;

/* [create_logic_tab n x] returns an array indexed from 0 to n-1, 
 * with all cells equals to [x] 
 **/
//@ logic logic_tab create_logic_tab(n: integer, x:double);

/*

interface PersistentArrayInterface {

    //@ model logic_tab model_tab;
  
    /*@ requires n >= 0;
      @ ensures \result.model_tab == create_logic(n,0.0);
      @* /
    static PersistentArray create(int n);

    
    /*@ requires 0 <= i < length(model_tab);
      @ assigns \nothing;
      @ ensures \result == select(this.model_tab,i);
      @* /
    double get(int i);

    /*@ requires 0 <= i < length(model_tab);
      @ assigns \nothing;
      @ ensures \fresh(\result); 
      @ ensures \result.model_tab == store(this.model_tab,i,x);
      @* /
    PersistentArray set(int i, double x);

}

*/

abstract class Data {

    abstract double get(int i);
    
    abstract PersistentArray set(int i, double x, PersistentArray parent);

}

class Arr extends Data {

    double table[];

    //@ invariant table != null;

    Arr(int n) {
	table = new double[n];
    }

    double get(int i) {
	return table[i];
    }

    PersistentArray set(int i, double x, PersistentArray parent) {
	double old = table[i];
	table[i] = x;
	PersistentArray tmp1 = new PersistentArray(this);
	Data tmp2 = new Diff(i,old,tmp1);
	parent.contents = tmp2;
	return tmp1;
    }
}

class Diff extends Data {

    int index;
    double value;
    PersistentArray remaining;

    //@ invariant remaining != null;

    Diff(int i, double x, PersistentArray rem) {
	index = i;
	value = x;
	remaining = rem;
    }

    double get(int i) {
	if (i == index) return value;
	return remaining.get(i);
    }

    PersistentArray set(int i, double x, PersistentArray t) {
	Data tmp = new Diff(i,x,t);
	return new PersistentArray(tmp);
    }
}

public class PersistentArray // implements PersistentArrayInterface 
 {

    Data contents;

    //@ invariant contents != null;

    PersistentArray(Data d) {
	contents = d;
    }

    static PersistentArray create(int n) {
	return new PersistentArray(new Arr(n));
    }

    double get(int i) {
	return contents.get(i);
    }

    PersistentArray set(int i, double x) {
	return contents.set(i,x,this);
    }

    public static void main(String argv[]) {

	PersistentArray t1 = PersistentArray.create(10);
	PersistentArray t2 = t1.set(5,0.2);
	System.out.println("t1[5] = " + t1.get(5));
	System.out.println("t2[5] = " + t2.get(5));
    }

}






	
	
	
