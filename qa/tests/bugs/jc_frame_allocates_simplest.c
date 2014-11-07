#pragma SeparationPolicy(none)

struct obj {
  char *str;
} obj;


//@ assigns \nothing;
extern void *malloc(unsigned long size);

//@ assigns \nothing;
extern void free(void *addr);

//@ frees obj->str;
void fobj(struct obj *obj)
{
  free(obj->str);  
}
