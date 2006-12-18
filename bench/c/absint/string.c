
typedef unsigned int size_t;

void *malloc(size_t);

char *memcpy(char *s1, const char *s2, size_t n) {
  char *r = s1;
  while (n-- > 0) *s1++ = *s2++;
  return r;
}

char *memmove(char *s1, const char *s2, size_t n) {
  char *tmp = (char*)malloc(n * sizeof(char));
  memcpy(tmp,s2,n);
  memcpy(s1,tmp,n);
  return s1;
}

char *strcpy(char *s1, const char *s2) {
  char *r = s1;
  while (*s1++ = *s2++) ;
  return r;
}

char* strncpy(char *s1, const char *s2, size_t n) {
  char *r = s1;
  while ((n-- > 0) && (*s1++ = *s2++)) ;
  while (n-- > 0) *s1++ = 0;
  return r;
}

char *strcat (char *s1, const char *s2) {
  char *r = s1;
  while (*s1++) ;
  strcpy(s1,s2);
  return r;
}

char *strncat (char *s1, const char *s2, size_t n) {
  char *r = s1;
  while (*s1++) ;
  while ((n-- > 0) && (*s1++ = *s2++)) ;
  if (n > 0) *s1 = 0;
  return r;
}

/*
  (* Local Variables: *)
  (* compile-command: "caduceus -print-norm --loc-alias --arith-mem --abs-int -d string.c" *)
  (* End: *)
*/

