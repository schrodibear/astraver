/*

  BTS #41

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

  //@ loop invariant 0 <= i && i <= MAX;
  for (i = 0; i < MAX; i++) {
    a[i] = 0x45;
  }
}

/*@ assigns c[..];
 */
void assign_char(void)
{
  int i;

  //@ loop invariant 0 <= i && i <= MAX;
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

  //@ loop invariant 0 <= j;
  for(j=0; j<aLength; j++) {
    a[j] = 0;
  }
}


