typedef struct {
    int x;   
    int y;
} coord;

coord  tab [3];

void f (int x);

void g (int index)
{
    f((tab+index)->x);
    f(tab[index].x);
}
