
/*

C test file

*/

int x;
int y;

int f(int a, int b) /*@ writes x 
                        post result = a + b */;

int main() {
  x = 0;
  for (y = 0; y < 10; ++y)
    /*@ invariant x=y variant 10-y */
    x = 1;
}
