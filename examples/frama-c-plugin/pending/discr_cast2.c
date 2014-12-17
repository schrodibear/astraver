struct packet1; // forward declaration
struct packet2; // forward declaration

struct header {
    int discr;
};

struct packet1 {
    int discr;
    int val1;
};

struct packet2 {
    struct header head;
    float val2;
};

/*@ requires *p == 0 => p <: struct packet1;
  @       && *p == 1 => p <: struct packet2;
  @ */
void get(int *p, int *v1, float *v2) {
    switch (*p) {
        case 0: *v1 = ((struct packet1*) p)->val1; break;
        case 1: *v2 = ((struct packet2*) p)->val2; break;
    }
}
