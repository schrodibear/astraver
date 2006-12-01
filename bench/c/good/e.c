/* It is 84 characters long and calculates e to 992 decimal places: 

a[999],x,n;main(N){for(;n||(putchar(48^x),
n=998+--N);x+=10*a[--n]+!N)a[n]=x%n,x/=n;}

*/

void putchar(char);

int a[999],x,n;

void main(N){
  for(; n||(putchar(48^x), n=998+--N); x+=10*a[--n]+!N)
    a[n]=x%n,x/=n;
}
