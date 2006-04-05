typedef struct {
    int x;   
    int y;
} coord;

coord  tab [3];

/*@ assigns \nothing */
void f (int x);

/*@ requires 0 <= index < 3 */
void g (int index)
{
    f((tab+index)->x);
    f(tab[index].x);
}
