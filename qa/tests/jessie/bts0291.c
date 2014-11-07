/* Frama-C BTS 0080

Status: open

yields:
File "why/bts0291.why", line 617, characters 44-65:
Unbound variable bitvector_alloc_table

*/

// # pragma SeparationPolicy(None)


/*@ requires \valid(x) && \valid(y) ;
    assigns *x, *y ;
    ensures *y==2 && *x==-1 ;
*/
void foo(int *x, char *y) {
	*x=-1 ;
	*y=2 ;
}

void test1() {
	int x ;

	foo(&x,&x) ;	
        // pas valide pour jessie: le cast de pointeur viole l'hypothèse 
	// de séparation sur les types !

	//@ assert 2==-1  ;
}

/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0291.c"
End:
*/



