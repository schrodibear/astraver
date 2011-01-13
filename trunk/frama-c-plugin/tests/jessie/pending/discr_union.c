struct packet {
    int discr;
    union {
        int val1;
        float val2;
    } uni;
    /*@ invariant discr0(this) { 
      @      this->discr == 0 => this->uni <: this->uni.val1
      @ } */	   
    /*@ invariant discr1(this) { 
      @      this->discr == 1 => this->uni <: this->uni.val2 
      @ } */
};

void get(struct packet *p, int *v1, float *v2) {
    switch (p->discr) {
        case 0: *v1 = p->uni.val1; break;
        case 1: *v2 = p->uni.val2; break;
    }
}
