/* Frama-C BTS 0376


Status: closed


produced incorrect lemmas because this big constant becomes -1

*/

/*@ ensures \result == 1;
  @ */
int always_one(unsigned long long a) {
    if (a <= 0xFFFFFFFFFFFFFFFFull)
        return 1;
    return 0;
}


/*@ ensures \result == 1;
  @ */
int always_one2(unsigned long a) {
    if (a <= 0xFFFFFFFFul)
        return 1;
    return 0;
}


/*
Local Variables:
compile-command: "make bts0376"
End:
*/
