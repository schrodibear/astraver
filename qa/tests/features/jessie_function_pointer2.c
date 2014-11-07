int (*fptr)(int, char **);
   
//@ decreases argc;
int
main(int argc, char **argv)
{
   static int i = 0;
   if (i > 1000000) i = 0;
   
   if (!i++ && argc > 0) {
      fptr = &main;
      fptr(argc - 1, ((char **)0));
   }

   return 0;
}

