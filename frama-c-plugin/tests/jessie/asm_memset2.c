/* run.config
   COMMENT: don't run this test while it raises an assertion
   DONTRUN:
 */


/*@ lemma div4 :
  @   \forall integer x; x >= 0 ==> 4*(x/4) <= x;
  @*/

/*@ lemma div4_not_mod4 :
  @   \forall integer x; x > 0 && x % 4 != 0 ==> 4*(x/4) < x;
  @*/

/*@
requires i_min <= i_max <= 4294967294 ;
requires \valid_range(Adresse, i_min, i_max);
assigns Adresse[i_min..i_max];
ensures \forall integer k;
            i_min <= k <= i_max ==> Adresse[k] == ValOct;
*/
void memset_uchar
    (unsigned char * Adresse,
    const unsigned char     ValOct,
    const unsigned long int i_min,
    const unsigned long int i_max)
{
    unsigned long int i;
    
    /*@ loop invariant i_min <= i <= i_max+1 <= 4294967295 ;
        loop invariant
            \forall integer k;
                i_min <= k < i ==> Adresse[k] == ValOct;
     */
    for (i=i_min; i<=i_max; i++)
    {
        Adresse[i] = ValOct;
    } 
}


/*@
requires i_min <= i_max <= 4294967294 ;
requires \valid_range(Adresse, i_min, i_max);
ensures \forall integer k;
            i_min <= k <= i_max ==> Adresse[k] == ValMot;
*/
void memset_uint
    (unsigned long int * const  Adresse,
    const unsigned int          ValMot,
    const unsigned long int     i_min,
    const unsigned long int     i_max)
{
    unsigned long int i;
    
    /*@ loop invariant i_min <= i <= i_max+1 <= 4294967295 ;
        loop invariant
            \forall integer k;
                i_min <= k < i ==> Adresse[k] == ValMot;
     */
    for (i=i_min; i<=i_max; i++)
    {
        Adresse[i] = ValMot;
    } 
}


extern unsigned long int addr_mod4;

#define addr_mod(addr,mod) addr_mod4


/*@
requires 0 <= addr_mod4 <= 3;

requires 1 <= NbOct ;
requires \valid_range(((char *)Adresse), 0, NbOct-1);

behavior small_data :
    assumes NbOct < 4;
    ensures \forall integer k;
                0 <= k <= NbOct-1 ==> ((char *)Adresse)[k] == ValOct;

behavior misaligned_data :
    assumes NbOct >= 4;
    assumes addr_mod4 != 0;
    ensures \forall integer k;
                0 <= k <= (3-addr_mod4) ==> ((char *)Adresse)[k] == ValOct;
    ensures
        \forall integer k;
            (4-addr_mod4) + 4*((NbOct-(4-addr_mod4))/4) <= k <= NbOct-1
            ==> ((char *)Adresse)[k] == ValOct;

behavior aligned_data :
    assumes NbOct >= 4;
    assumes addr_mod4 == 0;
    ensures
        \forall integer k;
            4*(NbOct/4) <= k <= NbOct-1 ==> ((char *)Adresse)[k] == ValOct;
*/
void memset_burst4
    (void * const           Adresse,
    const unsigned char     ValOct,
    const unsigned long int NbOct)
{
    unsigned char *s=Adresse;
    unsigned long int index_oct=0;
    
    if (NbOct >= 4)
    {
        unsigned long int align = 4 - addr_mod(s,4);
        unsigned long int nb_mots_alignes;
        
        if (align < 4)
        {
            memset_uchar(s, ValOct, index_oct, align-1);
            /*@ for misaligned_data:
                    assert \forall integer k;
                        0 <= k <= (3-addr_mod4) ==> s[k] == ValOct;
            */
            index_oct += align;
        }
        nb_mots_alignes=(NbOct-index_oct)/4;
        //memset_uint(s+index_oct, 16843009*ValOct, 0, nb_mots_alignes-1);
        index_oct += 4*nb_mots_alignes;
    }
    
    memset_uchar(s, ValOct, index_oct, NbOct-1);
}
