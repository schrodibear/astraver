#include <wchar.h>
#include <stdio.h>

/*@ assigns \nothing;*/
int printf(const char *s, ...);

struct pair {
  int i;
  const char *s;
};

struct pair pair_arr[]  = {
  {1, "First global string"},
  {2, /*@ proxy2 = */"Second global string"},
  {3, "Third global string"},
  {4, /*@ proxy4 = */ "Fourth global string"},
  {1, "Fifth global string"}};

//@ global invariant valid_pair_arr: \valid(pair_arr+(0..3));

const char *str = "global string";
char str2[] = "global string 2";

const char *un = "unique str";

//@ ghost const char * const proxy1 __attribute__ (( __literal )) = &"First glob...";
//@ ghost const char * const proxy3 __attribute__ (( __literal (0) )) = "Thi";


int f1 ()
{

  //@ ghost static const char * const proxy5 __attribute__ (( __literal (f1, 0) )) = "First ...";
  //@ ghost static const char * const proxy6 __attribute__ (( __literal (f1, 1) )) = "First ...";

  //@ ghost static const char * const proxy7 __attribute__ (( __literal (f2, 1) )) = "Fif...";
  //@ ghost static const int * const proxy8 __attribute__ (( __literal (f2) )) = L"First...";

  //@ assert proxy5 != \null && proxy7 != \null;

  //@ assert proxy6 != \null && proxy8 != \null;

  const char * s1 = "First local string";
  const char * s2 = "First local string";
  return 0;

}

int f2 ()
{
  const int * s1 = L"First local string";
  const char * s2 = "Fifth global string";
  const char * s3 = /*@ proxy11 = */ "Fifth global string";
  //@ assert proxy11[3] == 't';
  return 1;
}

int main()
{
  //@ ghost static const char * const non_proxy10 = "First";

  //@ assert proxy1 != \null;
  //@ assert proxy2[0] == 'S';
  //@ assert proxy3 != 0;
  //@ assert *proxy4 == 'F';

  const int * p = /*@ proxy9 = */ L"The seminar was completely screwed up!";
  //@ assert proxy9[0] == 'T';
  printf("%s %S", "ssss");
}
