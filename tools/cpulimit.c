
#include <sys/resource.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>


int main(int argc, char *argv[]) {
  int limit;
  struct rlimit res;

  if (argc < 3) {
    fprintf(stderr,"usage: %s <time limit in seconds> <command>\n",argv[0]);
    return 1;
  }
  /* get time limit in seconds from command line */
  limit = atoi(argv[1]);

  /* set the CPU limit */
  getrlimit(RLIMIT_CPU,&res);
  res.rlim_cur = limit;
  setrlimit(RLIMIT_CPU,&res);
    
  /* exec the command */
  execvp(argv[2],argv+2);
  return errno;
}
