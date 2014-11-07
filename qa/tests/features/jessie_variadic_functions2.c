#include <stdarg.h>
#include <stdio.h>

void empty_variadic(int n, ...)
{
}

void recursive_variadic(const int n1, int *n2, const char *spec, ...)
{
	va_list vl1, vl2;
	int i, c, cc = 4;

        printf("%d\n", *n2);
	*n2 += cc;
        printf("%d\n", *n2);
	if (n1 == 0) return;
	
	va_start(vl1, spec);
	for ( i = 0; i < n1; i++) {
		c += va_arg(vl1, long int);
		c += va_arg(vl1, int);
		if (c > 0) {
			cc++;
		}
	}
	va_copy(vl2, vl1);
	*n2 += cc;
        printf("%d\n", *n2);
	recursive_variadic(n1 - 1, n2, spec, c, cc);
        n2 += 10;
	va_end(vl1);
	empty_variadic(1);
	empty_variadic(1);
	empty_variadic(0, "1");
}

/* this function will take the number of values to average
   followed by all of the numbers to average */
double average ( int num, ... )
{
    va_list arguments;                     
    double sum = 0;
    int x;

    /* Initializing arguments to store all values after num */
    va_start ( arguments, num );           
    /* Sum all the inputs; we still rely on the function caller to tell us how
     * many there are */
    for ( x = 0; x < num; x++ )        
    {
        sum += va_arg ( arguments, double ); 
    }
    va_end ( arguments );                  // Cleans up the list

    return sum / num;                      
}

int main(char *const argv[])
{
    /* this computes the average of 13.2, 22.3 and 4.5 (3 indicates the number of values to average) */
    printf( "%f\n", average ( 3, 12.2, 22.3, 4.5 ) );
    /* here it computes the average of the 5 values 3.3, 2.2, 1.1, 5.5 and 3.3 */
    printf( "%f\n", average ( 5, 3.3, 2.2, 1.1, 5.5, 3.3 ) );
    
    int n2 = 0;
    recursive_variadic(1, &n2, "", 4l, (int)'f', 5l, (int)'g');
    printf( "%d\n", n2);
    return 0;
}

