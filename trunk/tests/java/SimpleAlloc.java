class Node {
    int val;

    //@ assigns this.val;
    Node(){}
}

class test {
    Node[] x;

    /*@ requires x!=null && x.length==10  ;
      @ assigns x[0];
      @ ensures x!=null;
      @*/
    void test() {
        x[0]=new Node();
    }
}
