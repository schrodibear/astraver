typedef struct las3
{
  int  c;
} las3;

typedef struct las2
{
  las3    b[3];
  
} las2;

typedef struct las1
{
  las3  b;
  
} las1;

typedef struct las
{
  las1    a;
} las;

