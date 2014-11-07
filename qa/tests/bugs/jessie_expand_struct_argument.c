struct s {
	int a, b;
};


int f (struct s s);

int main(void) {
	struct s s;
	int r = f(s);
	return r;
}
