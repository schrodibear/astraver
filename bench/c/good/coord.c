typedef struct {
    int x;   
    int y;
} coord;

coord  tab [3];
/*@ invariant tab_range : \valid_range(tab,0,2) */

/*@ assigns \nothing */
void f (int x);

/*@ requires 0 <= index < 3 */
void g (int index)
{
    f((tab+index)->x);
    f(tab[index].x);
}
