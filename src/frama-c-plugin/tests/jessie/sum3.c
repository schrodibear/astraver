typedef unsigned char UINT8;

typedef struct {
UINT8 a[3];
UINT8 Sum[3];
UINT8 b[3];
} S;

S vect;

/*@ requires \valid(vect.a+(0..2)) && \valid(vect.Sum+(0..2)) && \valid(vect.b+(0..2));
  @ requires \forall integer i,j; 0 <= i <= 2 && 0 <= j <= 2 ==>
  @    vect.a + i != vect.b + j && vect.a + i != vect.Sum + j && vect.b + i != vect.Sum + j;
 @ assigns vect.a[0..2], vect.Sum[0..2], vect.b[0..2];
 @ ensures \forall integer m; 0 <= m < 3 ==> vect.Sum[m] == vect.a[m] + vect.b[m];
 @*/
void f(){

  /*@ assigns vect.a[0..2], vect.b[0..2];
    @*/
  { vect.a[0] = 1;
    vect.a[1] = 2;
    vect.a[2] = 3;
    vect.b[0] = 4;
    vect.b[1] = 5;
    vect.b[2] = 6;
  }

//@ assert \forall integer m; 0 <= m < 3 ==> vect.Sum[m] == \at(vect.Sum[m],Pre);


/*@ loop invariant 0 <= i <= 3;
@ loop invariant \forall integer m; 0 <= m < 3 ==> vect.a[m]==\at(vect.a[m],Here) && vect.b[m]==\at(vect.b[m],Here);
@ loop invariant \forall integer m; i <= m < 3 ==> vect.Sum[m] == \at(vect.Sum[m],Pre);
@ loop invariant \forall integer m; 0 <= m < i ==> vect.Sum[m] == vect.a[m] + vect.b[m];
@ // loop assigns vect.Sum[0..2];
@ loop variant 3-i;
@*/
for (UINT8 i=0; i < 3; ++i) {
vect.Sum[i] = vect.a[i] + vect.b[i];
}
}
