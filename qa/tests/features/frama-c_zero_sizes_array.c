

struct s {
	int a[5];
	char array[];
} s1[3];

struct expandable {
	int length;
	int contents[0];
} *expndbl;

//@assigns \nothing;
extern void * malloc(unsigned int s);

/*@ ensures \result >= 0 && \result <= 1000;
  @ assigns \nothing;
  */
int arbitrary() 
{
	int a;
	return a > 0 ? a < 1000 ? a : 1000 : 4;
}

int main()
{
	int len = arbitrary();
	//@ assert sizeof(s1) == 60;
	expndbl = malloc (sizeof (struct expandable) + len * sizeof (int));
        if (len > 5) {
          expndbl->contents[5] = 55;
        }
        s1[2].a[1] = 5;
        if (len > 5) {
          //@ assert expndbl->contents[5] == 55;
        }
	return 0;
}
