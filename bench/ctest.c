
/*

C test file

*/

int x;
int y;

int f(int a, int b) /*@ writes x 
                        post result = a + b */;

int main() {
  x = f(x,y);
}
