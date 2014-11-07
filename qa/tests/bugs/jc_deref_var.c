

//@ assigns \nothing;
int f1 (int a)
{
}

//@assigns \nothing;
int f2 (int b)
{
 b = 2;
 //@ assert b == 2;
}

