#pragma SeparationPolicy(regions)
int *asg;

//@ requires \valid(src);   requires src == eql;
void ftest(int *src,int *eql)
{
    asg = src;
    //@ assert \valid(asg);
    //@ assert \valid(eql);
    //@ assert *src == *asg;
    //@ assert *src == *eql;
}
  
