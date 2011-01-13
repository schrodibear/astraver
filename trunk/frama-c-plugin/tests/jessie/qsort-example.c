#include <stdlib.h>


//**** rappel :
void qsort(void* base,
           size_t nmemb,
           size_t size,
           int(*compar)(const void *, const void *));



//**** client code:


struct date {
  int day;
  int month;
  int year;
};


int compare_by_year(const struct date *x, const struct date *y) {
  if (x->year < y->year) return -1;
  if (x->year == y->year) return 0;
  return 1;
}


int compare_for_qsort(const void *x, const void *y) {
  return compare_by_year((struct date *)x,(struct date *)y);
}


#include <stdio.h>
#include <assert.h>

int main() {
  struct date b[] = { {1,1,2010} , { 2,2, 2009}, {3,3,2010}};
  qsort(b,3,sizeof(struct date),&compare_for_qsort);
  assert(b[0].year <= b[1].year);
  printf("OK\n");
  return 0;
}




/*
Local Variables:
compile-command: "gcc -std=c99 -Wall qsort-example.c && ./a.out"
End:
*/
