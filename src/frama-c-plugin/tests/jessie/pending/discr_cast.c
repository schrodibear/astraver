struct packet1; // forward declaration
struct packet2; // forward declaration

struct header {
    int discr;
    /*@ invariant discr0(this) {
      @      this->discr == 0 => this <: struct packet1
      @ } */
    /*@ invariant discr1(this) {
      @      this->discr == 1 => this <: struct packet2
      @ } */
};

struct packet1 {
    int discr;
    int val1;
};

struct packet2 {
    struct header head;
    float val2;
};

/*@ requires \forall int x; x == x &&  \forall int x; x == x; */
void get(struct header *p, int *v1, float *v2) {
    switch (p->discr) {
        case 0: *v1 = ((struct packet1*) p)->val1; break;
        case 1: *v2 = ((struct packet2*) p)->val2; break;
    }
}
