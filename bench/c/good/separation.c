
struct s {
  int t[2];
  int u[3];
} s;

int v[4];

//@ ensures \result == 1
int f() {
  s.t[0] = 1;
  s.u[0] = 2;
  v[0] = 3;
  return s.t[0];
}

int g(){
  return v[0];
}


struct {
  int x[1];
} tab[5];


int h(){
  return tab[0].x[0];
}
