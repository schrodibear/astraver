struct s {
	int a, b;
};

/*@ requires \valid(s1) && \valid(pi);
  @ assigns s1->a;
*/
void f(struct s *s1, int *pi);

int main()
{
	struct s s;
	struct s * ps = &s;
	f(&s, &s.a);	
	f(&s, &s.a);
	return 0;
}
