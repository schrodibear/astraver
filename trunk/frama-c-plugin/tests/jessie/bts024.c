
#define cellMax		1024
#define cellWd		5
#define cellNil		cellMax		// should better be -1
#define NULL		((void*)0)



struct _alloc {
    int top;		// first unused index
    int fre;		// start index of free-list
    int userCnt;	// number of cell given to user; should be ghost
    int buf[cellMax*cellWd];
};



/*@ axiomatic a1 {
    logic boolean isList{L}(int *b, integer f);
    logic integer lgth{L}(int *b, integer f);
    axiom a2{L}:
	\forall int *b, integer f;
	    isList(b,f) <==> f == cellNil || isList(b,\at(b[f*cellWd],L));
    axiom a3{L}:
	\forall int *b; lgth(b,cellNil) == 0;
    axiom a4{L}:
	\forall int *b, integer f; 
	    f != cellNil ==> lgth(b,f) == lgth(b,b[f*cellWd]) + 1;
}
*/



static struct _alloc a = { 0, cellNil, 0 };
/*@ global invariant inv1: isList(a.buf,a.fre);
    global invariant inv2: lgth(a.buf,a.fre) + a.userCnt == a.top;
    global invariant inv3: 0 <= lgth(a.buf,a.fre) <= a.top;
    global invariant inv4: 0 <= a.userCnt <= a.top;
*/



/*@ behavior empty:
	assumes a.userCnt >= cellMax;
	ensures \result == NULL;
    behavior nonEmpty:
	assumes a.userCnt < cellMax;
	ensures a.userCnt == \old(a.userCnt) + 1;
	ensures \valid_range(\result,0,cellWd-1);
*/
int *allocCells(void)
{
    if (a.fre != cellNil) {
	int * const res = &a.buf[a.fre*cellWd];
	a.fre = a.buf[a.fre*cellWd];
	a.userCnt += 1;
	return res;
    } else if (a.top < cellMax) {
	int * const res = &a.buf[a.top*cellWd];
	a.top += 1;
	a.userCnt += 1;
	return res;
    } else {
	return NULL;
    }
}



/*@ requires a.userCnt > 0;
    ensures a.userCnt == \old(a.userCnt) - 1;
*/
void freeCells(int *cAdr)
{
    int const cIdx = cAdr - a.buf;
    a.buf[cIdx*cellWd] = a.fre;
    a.fre = cIdx;
    a.userCnt -= 1;
}

