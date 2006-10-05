const int c = 5;

const int t[] = {1,2,3,4};

/*@ ensures \result == 8 */
int f (){
  return c+t[2];
}



struct T {
  int x;
  int y;
  int z[3];
};

const struct T x = {5,6,{1,2,3}};

/*@ ensures \result == 3*/
int g(){
  return x.z[2];
}



struct U {
  int x;
  const int y;
};

struct U y = { 1, 2 };

/*@ ensures \result == 2 */
int h() { return y.y; }


struct V {
  int t1[2];
  int t2[1];
};

struct V w = {{1, 2},{3}};


/*@ ensures \result == 1 */
int i (){
  w.t1[0] = 1;
  w.t2[0] = 2;
  return w.t1[0];
}

const int N = 100;
int t2[N];

void j() { return t2[99]; }

enum E { A,B,C };
const enum E e = B;

//@ ensures \result == B
enum E k() { return e; }
