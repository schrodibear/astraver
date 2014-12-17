int s;

//@ assigns \nothing;
void f1(int * p);
//@ assigns \nothing;
void f2(int * p);

void main()
{
	s=1;
	//@ assigns \nothing;
	{
		f1(&s);
		f2(&s);
	}
	//@ assert s==1;
}
