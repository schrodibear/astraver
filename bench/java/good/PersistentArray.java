

//@ type logic_tab;

/* [create_logic_tab n x] returns an array indexed from 0 to n-1, 
 * with all cells equals to [x] 
 **/
//@ logic logic_tab create_logic_tab(n: integer, x:double);

interface PersistentArray {

    //@ model logic_tab model_tab;
  
    /*@ requires n >= 0;
      @ ensures \result.model_tab == create_logic(n,0.0);
      @*/
    static PersistantArray create(int n);

    
    /*@ requires 0 <= i < length(model_tab);
      @ assigns \nothing;
      @ ensures \result == select(this.model_tab,i);
      @*/
    double get(int i);

    /*@ requires 0 <= i < length(model_tab);
      @ assigns \nothing;
      @ ensures \fresh(\result); 
      @ ensures \result.model_tab == store(this.model_tab,i,x);
      @*/
    PersistantArray set(int i, double x);

}


abstract class Data {

    double get(int i);

}

class Arr extends Data {

    double t[];

    //@ invariant t != null;

    double Arr(int n) {
	t = new double[n];
    }

    double get(int i) {
	return t[i];
    }

}

class Diff extends Data {

    int index;
    double value;
    Data remaining;

    //@ invariant remaining != null;

    double get(int i) {
	if (i == index) return value;
	return remaining.get(i);
    }

}


class PersistantArrayImpl {

    Data contents;

    //@ invariant contents != null;

    PersistantArrayImpl(int n) {
	contents = new Arr(n);
    }


    static PersistantArrayImpl create(int n) {
	return new PersistantArrayImpl(n);
    }

    double get(int i) {
	contents.get(i);
    }

    PersistantArrayImpl set(int i, double x) {

    }

}





implantation:

   type data = Arr of int array 
    | Diff of int * int * tab  

   and tab = data ref   

   logic repr (t:tab) (tt:tab_logic) =
       repr_data !t tt

   and repr_data (d:data) (tt:tab_logic) =
       match d with
        | Arr a ->   
           forall i, 0 <= i < Array.length a ==>
              Array.get a i == logic_array_get tt i
        | Diff (i,v,t') ->
              (* conditions sur indice i ? *)
              forall tt', repr t' tt' ==>
                repr_data d (logic_array_update tt' i v)        

   let create n = ref (Arr (Array.create n 0)) 

  val set : (t:tab) -> TODO

  val get : (t:tab) -> TODO
