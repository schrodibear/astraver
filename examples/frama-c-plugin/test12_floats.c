
double x;
float y;

/*@ ensures x == 1.0;
  @ ensures y == 1.0;
  @*/
void f() {
  x = 1.0/3.0+1.0/3.0+1.0/3.0;
  y = 1.0f/3.0f+1.0f/3.0f+1.0f/3.0f;
}

/*@ ensures x == 9.0;
  @ ensures y == 9.0;
  @*/
void g() {
  x = 1.0*3.0+1.0*3.0+1.0*3.0;
  y = 1.0f*3.0f+1.0f*3.0f+1.0f*3.0f;
}



