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
  {2, "Second global string"},
  {3, "Third global string"},
  {4, "Fourth global string"},
  {1, "Fifth global string"}};

const char *str = "global string";
char str2[] = "global string 2";

const char *un = "unique str";

/*@ axiomatic dummy_usages {
  @    logic boolean dummy_usage = pair_arr != \null || str != \null || str2 != \null || un != \null;
  @ }
  @*/


//@ ghost const char * const proxy1 __attribute__ (( __literal )) = &"First glob...";
//@ ghost const char * const proxy2 __attribute__ (( __literal (0), __invariant )) = &"Sec...";
//@ ghost const char * const proxy3 __attribute__ (( __literal (0) )) = "Thi";
//@ ghost const char * const proxy4 __attribute__ (( __literal, __invariant )) = &"Four";


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

//@ assigns \nothing;
int f2 ()
{
  const int * s1 = L"First local string";
  const char * s2 = "Fifth global string";
  const char * s3 = "Fifth global string";
  return 1;
}

//@ ghost static const wchar_t * const proxy9 __attribute__ (( __literal, __invariant )) = &L"The semi...";

int main()
{
  //@ ghost static const char * const non_proxy10 = "First";
  //@ ghost static const char * const proxy11 __attribute__ (( __literal (f2, 1), __invariant )) = "Fif...";

  //@ assert proxy11[3] == 't';

  //@ assert proxy1 != \null;
  //@ assert proxy2[0] == 'S';
  //@ assert proxy3 != 0;
  //@ assert *proxy4 == 'F';

  //@ assert proxy9[0] == 'T';
  const int * p = L"The seminar was completely screwed up!";
  printf("%s %S", "ssss");
}
