

#define BUFF_SIZE 4

/*@ requires \valid(msg+(0.. BUFF_SIZE));
    ensures msg[BUFF_SIZE] == '\0';
*/
int setFoo(char* msg) {
  msg[BUFF_SIZE] = '\0';
  msg[BUFF_SIZE-1] = '\0';
  return 0;
}
