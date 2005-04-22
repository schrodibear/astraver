
/* these programs _are_ incorrect
   they are here to test the consistence of the theory */

struct u{int x;};

struct v{struct u x; int y[5];};

struct v * z;
struct u zz;

int x[4];
int y[5];

/*@ ensures \false */
void false1() {
  z->y[5] = 3;
  x[-1] = 1;
  y[5] = 2;
}
