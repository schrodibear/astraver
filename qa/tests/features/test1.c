typedef struct {
	int a, b;
} type_t;

/*@	assigns *((type_t *) buffer);
*/
int test(void *buffer)
{
	return 0;
}
