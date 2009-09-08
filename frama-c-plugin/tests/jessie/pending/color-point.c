
typedef struct { int x; int y; } Point;
typedef struct { int x; int y; int c; } ColorPoint;

//@ requires \valid(pt) && \typeof(pt) == \type(ColorPoint*);
int get_color(Point *pt) {
  return ((ColorPoint*)pt)->c;
}

/*
Local Variables:
compile-command: "LC_ALL=C make -j color-point"
End:
*/
