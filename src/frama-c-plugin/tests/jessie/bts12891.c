
void f () {
int i = 0;
//@ ghost L:
i = 1;
/*@ assert \at(i, L) == 0; */
}
