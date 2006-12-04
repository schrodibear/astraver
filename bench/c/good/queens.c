
//@ logic int bit(int x, int i)

//@ logic int nbits(int x)

//@ axiom nbits_nonneg : \forall int x; nbits(x) >= 0

//@ axiom nbits_zero : nbits(0) == 0

//@ logic int lowest_bit(int x)

/*@ axiom lowest_bit_def : 
  @   \forall int x; x != 0 => 
  @     \exists int i; (i >= 0 && 
  @                     lowest_bit(x) == bit(x,i) &&
  @                     bit(x,i) != 0 &&
  @                     \forall int j; 0 <= j < i => bit(x,j) == 0)
  @*/

/*@ axiom lowest_bit_zero :
  @   \forall int x; lowest_bit(x) == 0 <=> x == 0
  @*/

/*@ axiom lowest_bit_trick :
  @   \forall int x; x & -x == lowest_bit(x)
  @*/

/*@ axiom remove_one_bit :
  @    \forall int x, int i; 
  @       bit(x,i) != 0 => nbits(x - bit(x,i)) == nbits(x) - 1
  @*/

/*@ ensures \result == nbits(x) */
int count_bits(int x) {
  int d = 0, c = 0;
  /*@ invariant c + nbits(x-d) == nbits(\at(x,init))
    @ variant   nbits(x-d)
    @*/
  while (d = (x-=d) & -x) c++;
  return c;
}

// @ ghost int sol[][]

/****
t(a,b,c){int d=0,e=a&~b&~c,f=1;if(a)for(f=0;d=(e-=d)&-e;f+=t(a-d,(b+d)*2,(
c+d)/2));return f;}main(q){scanf("%d",&q);printf("%d\n",t(~(~0<<q),0,0));}
****/

int t(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  if (a)
    for (f=0; d=(e-=d)&-e; f+=t(a-d,(b+d)*2,(c+d)/2));
  return f;
}

int queens(int n) {
  return t(~(~0<<n),0,0);
}
