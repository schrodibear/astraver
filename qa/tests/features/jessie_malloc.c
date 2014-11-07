
extern void *malloc(unsigned long size);


/*@ ghost struct point { float x; float y; }; */;

/*@  type int_list = struct point ; */

// logic int_list origin = { .x = 0.0, .y = 0.0 };


/*@ ensures \result == \null || \valid(\result+(0..3)); */
int *f()
{
  int * ia = malloc(sizeof(int) * 4);
  if (!ia) {
    return 0;
 }
 return ia;
}
