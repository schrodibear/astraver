#include <stdlib.h>

/*@ allocates \nothing;*/
void t(void) {
    int *p = malloc(sizeof(*p) * 100);
}
