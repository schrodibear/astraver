/* Frama-C BTS 0041

version bis: explicit loop assigns clause

Status: closed


 */


# pragma JessieIntegerModel(exact)

#include <string.h>

#define MAX 12

int a[MAX];
char *c[MAX];

/*@ assigns a[..];
 */
void assign_int(void)
{
  int i;

  /*@ loop invariant 0 <= i && i <= MAX;
    @ loop assigns a[..];
    @*/
  for (i = 0; i < MAX; i++) {
    a[i] = 0x45;
  }
}

/*@ assigns c[..];
 */
void assign_char(void)
{
  int i;

  /*@ loop invariant 0 <= i && i <= MAX;
    @ loop assigns c[..];
    @*/
  for (i = 0; i < MAX; i++) {
    c[i] = strndup("something", MAX);
  }
}

/*@ assigns a[..];
    assigns c[..];
 */
void main(void)
{
  assign_int();
  assign_char();
}


/*@ requires \valid(a+ (0..aLength-1));
    assigns a[..];
*/
void foo(int a[], int aLength) {
  int j;

  /*@ loop invariant 0 <= j;
    @ loop assigns a[..];
    @*/
  for(j=0; j<aLength; j++) {
    a[j] = 0;
  }
}




/* 
Local Variables:
compile-command: "make bts0041-bis"
End:
*/
