

int x;


int f() {
  return x++;
}


int main() {
  int y;
  x = 3;
  if (f()) {
    y = 1;
  }
  else {
    y = 5;
    //@ assert \false;
  }
  //@ assert y==1;
}
