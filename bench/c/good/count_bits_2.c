/****** abstract sets of integers *******************************************/

//@ type iset

//@ predicate in_(int x, iset s)

//@ logic int card(iset s)
//@ axiom card_nonneg : \forall iset s; card(s) >= 0

//@ logic iset empty()
//@ axiom empty_card : \forall iset s; card(s)==0 <=> s==empty()

//@ logic iset remove(int x, iset s)
/*@ axiom remove_card : 
  @   \forall iset s; \forall int i;
  @     in_(i,s) => card(remove(i,s)) == card(s) - 1
  @*/

//@ logic int min_elt(iset s)
/*@ axiom min_elt_def : 
  @   \forall iset s; card(s) > 0 => in_(min_elt(s), s)
  @*/

/****** interpretation of C ints as abstract sets of integers ***************/

//@ logic iset iset(int x)

//@ axiom iset_c_zero : \forall int x; iset(x)==empty() <=> x==0

/*@ axiom iset_c_minus : 
  @   \forall int x, int a; 
  @     in_(x, iset(a)) => iset(a-x) == remove(x, iset(a))
  @*/

/*@ axiom iset_c_lowest_bit :
  @   \forall int x; x != 0 => x&-x == min_elt(iset(x))
  @*/
/*@ axiom iset_c_lowest_bit_help :
  @   \forall int x; x != 0 <=> x&-x != 0
  @*/

/**** count_bits ************************************************************/

/*@ ensures \result == card(iset(x)) */
int count_bits(int x) {
  int d = 0, c = 0;
  /*@ invariant c + card(iset(x-d)) == card(iset(\at(x,init)))
    @ variant   card(iset(x-d))
    @*/
  while (d = (x-=d) & -x) c++;
  return c;
}
