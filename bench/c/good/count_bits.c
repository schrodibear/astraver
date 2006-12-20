
// the i-th bit of x as 0 or 2^i
//@ logic int bit(int x, int i)

// the number of bits 1 in x
//@ logic int nbits(int x)

//@ axiom nbits_nonneg : \forall int x; nbits(x) >= 0

//@ axiom nbits_zero : nbits(0) == 0

// the lowest bit 1 in x
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
  int d, c;
  /*@ invariant c + nbits(x) == nbits(\at(x,init))
    @ variant   nbits(x)
    @*/
  for (c = 0; d = x&-x; x -= d) c++;
  return c;
}
