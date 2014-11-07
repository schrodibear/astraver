enum e1 {ZERO, ONE, TWO} e1_global;

enum e2 {ONE2 = 1, THREE = 3, FOUR};

enum e3 {ONE3 = 1, FIVE = 5, SIX};

struct inner {
	enum e2 f1;
	enum e3 *f2;
};

typedef struct inner inner_t;

struct outer {
	inner_t **f1;
};

typedef struct outer outer_t;

/*@ ghost outer_t **outer_global[4];
*/

/*@
  axiomatic f {
	  logic integer f reads outer_global;
  }
*/

void main1 ()
{
}

int main2 ()
{
	e1_global = 1;
	//@ assert e1_global == 1;
	return 0;
}
