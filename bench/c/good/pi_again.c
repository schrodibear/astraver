/* 112 characters long and calculates pi to 2880 decimal places: 

g,o,p,i=1e4,a[10001];main(x){for(;p?g=g/x*p+a[p]*i+2*!o:
53^(printf("%.4d",o+g/i),p=i,o=g%i);a[p--]=g%x)x=p*2-1;}

*/

void printint(int);

int g,o,p,i=1e4,a[10001];

void main(x) {
  for(; p?g=g/x*p+a[p]*i+2*!o: 53^(printint(o+g/i),p=i,o=g%i); a[p--]=g%x)
    x=p*2-1;
}
