#include <stdarg.h>
#include <stdio.h>

void *malloc(unsigned long size);

/* this function will take the number of values to average
   followed by all of the numbers to average */
double average ( int num, void *va_list)
{
    void *arguments;                     
    double sum = 0;
    int x;

    /* Initializing arguments to store all values after num */
    arguments = va_list;
    /* Sum all the inputs; we still rely on the function caller to tell us how
     * many there are */
    for ( x = 0; x < num; x++ )        
    {
        /*double *va_list_ = (double *) va_list;
          double result = *va_list_;
          va_list_ = va_list_ + 1;
          va_list = (void *) va_list_;*/
        double result = *(double *) va_list;
        va_list = ((double *) va_list) + 1;
        sum += result; 
    }
    ;                  // Cleans up the list

    return sum / num;                      
}

int main()
{
    void *va_list;
    va_list = malloc(sizeof (double) * 3);
    ((double *) va_list)[0] = 0.0f;
    ((double *) va_list)[1] = 22.3f;
    *(((double *)(((double *) va_list) + 1)) + 1) = 4.5f;
    /* this computes the average of 13.2, 22.3 and 4.5 (3 indicates the number of values to average) */
    average ( 3, va_list);
    /* here it computes the average of the 5 values 3.3, 2.2, 1.1, 5.5 and 3.3 */
    //printf( "%f\n", average ( 5, 3.3, 2.2, 1.1, 5.5, 3.3 ) );
}

