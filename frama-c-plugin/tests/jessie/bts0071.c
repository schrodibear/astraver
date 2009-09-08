

void myfun(int p){
    p = 1;
    //@ ghost Mylabel:
    p = 2;
    //@ assert \at(p,Mylabel)==p-1;
}
