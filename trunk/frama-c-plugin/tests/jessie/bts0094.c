/* Frama-C BTS 0094

Status: closed

*/

#include <limits.h>

char char_range(char i)
{
    //@ assert i >= CHAR_MIN;
    //@ assert i <= CHAR_MAX;
    return i;
}

signed char schar_range(signed char i)
{
    //@ assert i >= SCHAR_MIN;
    //@ assert i <= SCHAR_MAX;
    return i;
}

unsigned char uchar_range(unsigned char i)
{
    //@ assert i >= 0;
    //@ assert i <= UCHAR_MAX;
    return i;
}

short short_range(short i)
{
    //@ assert i >= SHRT_MIN;
    //@ assert i <= SHRT_MAX;
    return i;
}

unsigned short ushort_range(unsigned short i)
{
    //@ assert i >= 0;
    //@ assert i <= USHRT_MAX;
    return i;
}

/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0094.c"
End:
*/



