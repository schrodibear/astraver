struct s {
	int a, b;
};


//@ assigns \nothing;
int f (struct s s);

int main(void) {
	struct s s;
	int r = f(s);
	return r;
}
