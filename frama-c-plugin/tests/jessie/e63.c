
//typedef float TYP ;

#define TYP float

/* Tentatives de plusieurs théories : en espérant que cette dernière est correcte */

/*@

inductive incr{L}(TYP *t,integer i,integer j){

  case incr_ok{L}:
    \forall TYP *t; \forall integer i,j;
       i<j ==> t[i] <= t[i+1] ==> incr{L}(t,i+1,j) ==> incr{L}(t,i,j);

  case incr_alone{L}: \forall TYP *t;\forall integer i; incr{L}(t,i,i);

}

*/


/*@ predicate incr2{L}(TYP *t,integer i,integer j) =
  @   \forall integer k; i <= k < j ==> t[k] <= t[k+1];
  @*/

void f()
{
	TYP t[15]={2.,3.,5.,7.,7.,7.,7.,7.,8.,10.,12.,18.,18.,27.,28.};

/* Pour valider l'assert ci-dessous avec Alt-ergo, il semble qu'il
   faille découper l'intervalle [0;14] (case incr_union au-dessus est
   sensé faire l'union):
*/

// assert incr(t,12,14);
// assert incr(t,10,12);
// assert incr(t,8,10);
// assert incr(t,6,8);
// assert incr(t,4,6);
// assert incr(t,2,4);
// assert incr(t,0,2);

/* Bien entendu, on cherche à éviter ce découpage fastidieux en
   sous-intervalles */

//@ assert incr(t+0,0,14);

//@ assert incr2(t+0,0,14);


// Quid d'un intervalle encore plus grand ?
	TYP t2[100] = {
          0.,1.,2.,3.,4.,5.,6.,7.,8.,9.,
          10.,11.,12.,13.,14.,15.,16.,17.,18.,19.,
          20.,21.,22.,23.,24.,25.,26.,27.,28.,29.,
          30.,31.,32.,33.,34.,35.,36.,37.,38.,39.,
          40.,41.,42.,43.,44.,45.,46.,47.,48.,49.,
          50.,51.,52.,53.,54.,55.,56.,57.,58.,59.,
          60.,61.,62.,63.,64.,65.,66.,67.,68.,69.,
          70.,71.,72.,73.,74.,75.,76.,77.,78.,79.,
          80.,81.,82.,83.,84.,85.,86.,87.,88.,89.,
          90.,91.,92.,93.,94.,95.,96.,97.,98.,99.};

//@ assert incr(t2+0,0,99);

//@ assert incr2(t2+0,0,99);

}

/*
frama-c -jessie e63.c
*/
