struct inner {
	int a;
};
struct outer {
	struct inner inner;
	int b;
};

//@ assigns \nothing;
extern void *malloc(unsigned int size);

int main() {
	struct inner *pinner = malloc(sizeof (struct inner));
	pinner->a = 1;
	struct outer *pouter = malloc(sizeof (struct outer));
	pouter->inner.a = 2;
	//@ assert pouter->inner.a == 2;
	//@ assert pinner->a == 1;
}