

void buildMaze(uint n) {

  union_find u = create(n*n);

  //@ ghost integer num_edges = 0;

  /*@ loop invariant num_edges + NumClasses(u) == n*n;
    @*/
  while (num_classes(u) > 1) {
    uint x = rand() % n;
    uint y = rand() % n;
    uint d = rand() % 2;
    uint w = x, z = y;
    id (d == 0) w++; else z++;
    if (w < n && z < n) {
      int a = y*n+x, b = w*n+z;
      if (find(u,a) != find(u,b)) {
	// output_edge(x,y,w,z);
	//@ ghost num_edges++;
	union(a,b);
      }
    }
  }
  // nombre d'aretes = n*n - 1
  //@ assert num_edges == n*n - 1

  // each node is reachable from origin
  //@ assert \forall int x; 0 <= x < n*n ==> same(u,x,0);
}



