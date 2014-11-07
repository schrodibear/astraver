
//@ assigns \nothing;
extern void *malloc(unsigned long size);

//@ assigns \nothing;
extern void free(void *addr);

/*@ requires \valid(buf) && n > 0;
  @ ensures \valid((*buf)+(0..\old(n) -1)) && \fresh((*buf),\old(n));
  @ allocates *buf;
  @ assigns *buf;
 */
void alloc(char **buf, int n)
{
    *buf = malloc(n * sizeof(char));
}

/*@ requires \valid(buf) && \valid(*buf);
  @ ensures !\valid(*buf);
  @ frees *buf;
  @ assigns *buf;
 */
void _free(char **buf)
{
    free(*buf);
}

int main(int argc, char **argv)
{
    char *buf1, *buf2;
    char *buf;
    alloc(&buf1, 10);
    alloc(&buf2, 12);
    
    if (argc) {
       buf = buf1;
    } else {
       buf = buf2;
    }
    buf[9] = 'c';
    
    _free(&buf1);
    if (!argc) {
      buf[9] = 'c';
    }
}