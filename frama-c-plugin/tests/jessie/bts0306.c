/* Frama-C BTS 0306

Status: closed

yields:

Generating Why function strcmp_0
File "jc/jc_interp.ml", line 1831, characters 19-19:
Uncaught exception: File "jc/jc_interp.ml", line 1831, characters 19-25: Assertion failed

*/

# pragma JessieIntegerModel(math)

#include <jessie_prolog.h>

int strcmp(const char *s1, const char *s2)
        {
       while (*s1 == *s2++)
          if (*s1++ == 0)
        return (0);
       return (*(unsigned char *)s1 - *(unsigned char *)--s2);
    }


/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0306.c"
End:
*/
