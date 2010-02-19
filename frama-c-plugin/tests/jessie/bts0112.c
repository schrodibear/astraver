/* Frama-C BTS 0112

Status: closed

yields:


** Jc_interp_misc.transpose_location_list: TODO: parameters **
memory (mem-field(double_M),X_5)
in memory set (mem-field(double_M),A_4), (mem-field(double_M),X_5),
(mem-field(double_M),Y_6)
File "jc/jc_interp_misc.ml", line 737, characters 1-1:
Uncaught exception: File "jc/jc_interp_misc.ml", line 737, characters 1-7: Assertion failed

Fixed in Why 2.22

*/




typedef double fp;
#define FP_ESPILON DBL_EPSILON


/*@ axiomatic int_matrices {

  @ logic real pow_i(integer a, integer b);
  @ logic integer max_int;
  @ axiom max_int_eq: max_int == 0x1p53;

  @ predicate delay (integer n, integer p) =
  @   0 < n && 2 <= p &&
  @   (p-1)/2. * (pow_i(p, n-1) + pow_i(p-2, n-1)) <= max_int;

  @ axiom delay_decreases:
  @ \forall integer n1; \forall integer n2; 
  @     \forall integer p1; \forall integer p2;
  @   0 < n1 <= n2 ==> 2 <= p1 <= p2 
  @    ==> delay(n2,p2) ==> delay(n1,p1);  

  @ axiom delay_2: delay(55,2); 

  @ logic integer l_pmax(integer n); 

  @ axiom l_pmax_def: \forall integer n;  
  @    delay(n,l_pmax(n)) && !(delay(n,l_pmax(n)+1));

  @ axiom delay_pmax: \forall integer n; \forall integer p; 
  @    delay(n,p) ==>  p <= l_pmax(n); 

  @ } */


/*@ predicate is_exact_int_mat{L} (fp *X, integer LDX, integer N, integer M) =
  @   \valid_range(X,0,N*LDX+M) && 
  @   0 <= LDX && 0 <= N && 0 <= M  && M <= LDX  &&
  @   \forall integer i; \forall integer j; 0 <= i < N && 0 <= j < M ==>
  @      \round_error(X[i*LDX+j])==0 && \exists integer v;  X[i*LDX+j]==v; 

  @ predicate is_exact_int_mat_bounded_by{L}
  @ (fp *X, integer LDX, integer N, integer M, integer min, integer max) =
  @   \valid_range(X,0,N*LDX+M) && 
  @   0 <= LDX && 0 <= N && 0 <= M  && M <= LDX  &&
  @   \forall integer i; \forall integer j; 0 <= i < N && 0 <= j < M ==>
  @      \round_error(X[i*LDX+j])==0 && (\exists integer v;  X[i*LDX+j]==v)
  @         &&  min <= X[i*LDX+j] <= max; 

  @ predicate temporary_is_exact_int_mat_bounded_by{L}
  @ (fp *X, integer LDX, integer N, integer M, integer k, 
  @      integer min, integer max) =
  @   \valid_range(X,0,N*LDX+M) && 
  @   0 <= LDX && 0 <= N && 0 <= M  && M <= LDX  &&
  @   \forall integer i; \forall integer j; 
  @       ((0 <= i < N && 0 <= j < M) || (i==N && 0 <= j < k)) ==>
  @      \round_error(X[i*LDX+j])==0 && (\exists integer v;  X[i*LDX+j]==v)
  @         &&  min <= X[i*LDX+j] <= max;
  @*/


// ecrire une fonction Coq l_pmax débile mais CALCULATOIRE
// tabuler 2,3,4 (5?) et ensuite res++
// ou générer 2*55 axiomes
// pour 2<=n<=56 delay(n,..) et non delay(n, ..+1)


// Inductive solution to a unitary triangular system
/*@ requires 2 <= p && (p-1)*(p-1)*M <= max_int  &&
  @   \base_addr(Y) != \base_addr(A) &&
  @   (\forall integer i; \forall integer j; 
  @      0 <= i <= (N-1)*LDY+K-1 ==> 0 <= j <= (M-1)*LDX +K-1 ==> 
  @         Y+i != X+j ) &&
  @   is_exact_int_mat_bounded_by(Y,LDY,N,K,0,p-1) &&
  @   is_exact_int_mat_bounded_by(A,LDA,N,M,0,p-1) &&
  @   is_exact_int_mat_bounded_by(X,LDX,M,K,0,p-1);
  @ assigns Y[0..(N-1)*LDY+K-1];
  @ ensures 
  @   is_exact_int_mat_bounded_by(Y,LDY,N,K,(1-p)*(p-1)*M,p-1); 
  @ */
void DGEMM_NEG (int N, int M, int K, int p,
                fp *A, int LDA, fp *X, int LDX, fp *Y, int LDY) {
  int i, j, k;
  /*@ loop invariant 0 <= i <= N &&
    @    is_exact_int_mat_bounded_by(Y,LDY,i,K,(1-p)*(p-1)*M,p-1);
    @ loop assigns Y[0..(i-1)*LDY+K-1]; 
    @ */
  for (i = 0; i < N; i++)
    /*@ loop invariant 0 <= k <= K &&
      @   temporary_is_exact_int_mat_bounded_by(Y,LDY,i,K,k,(1-p)*(p-1)*M,p-1);
      @ loop assigns Y[i*LDY..i*LDY+(k-1)];
      @ */
      for (k = 0; k < K; k++) 
	/*@ loop invariant 0 <= j <= M &&
          @  \round_error(Y[i*LDY+k]) == 0 &&
          @  (\exists integer v;  Y[i*LDY+k]==v) &&
          @    (1-p)*(p-1)*j <= Y[i * LDY + k]  &&
	  @    Y[i * LDY + k] <= p-1; 
	  @ loop assigns Y[i*LDY+k];
	  @ */ 
	for (j = 0 ; j < M; j++)
	  Y[i*LDY+k] = Y[i*LDY+k] - A[i*LDA+j] * X[j*LDX+k];
      
}



/*@ requires is_exact_int_mat(X,LDX,N,K);
  @ assigns X[0..(N-1)*LDX+K-1];
  @ ensures is_exact_int_mat_bounded_by(X,LDX,N,K,0,p-1) &&
  @   \forall integer i; \forall integer j; 0 <= i < N && 0 <= j < K ==>
  @     \exists integer d; X[i*LDX+j] == \old(X[i*LDX+j]) + d*p;
  @*/
void DREMM (int N, int K, int p, fp *X, int LDX) {
  int i, k;
  for (i = 0; i < N; i++) for (k = 0; k < K; k++) {
    X[i*LDX+k] = fmod (X[i*LDX+k], p);
    if (X[i*LDX+k] < 0) X[i*LDX+k] += p; 
  }
}
//S: faisable, mais chiant, zappable



// Floating point exact solution to a small unitary triangular system
/*@ requires N <= 55 &&  
  @   is_exact_int_mat_bounded_by(X,LDX,N,K,0,l_pmax(N)-1) &&
  @   is_exact_int_mat_bounded_by(A,LDA,N,N,0,l_pmax(N)-1);
  @ assigns X[0..(N-1)*LDX+K-1];
  @ ensures
  @   is_exact_int_mat_bounded_by(X,LDX,N,K,-max_int,max_int);
  @*/
void DTRSM (int N, int K, fp *A, int LDA, fp *X, int LDX) {
  int i, j, k;
  for (i = N-2; i >= 0; i--)
    for (j = i+1; j < N; j++)
      for (k = 0 ; k < K; k++)
        X[i*LDX+k] = X[i*LDX+k] - A[i*LDA+j] * X[j*LDX+k];
}
//S: pour tout N <= 54, j'instancie N, je déroule et je gappa



/*@ requires 2 <= p;
  @  ensures delay(\result,p) && 
  @  (\forall integer q; 1 <= q <= \result <==> delay(q,p))
  @     &&  \result <= 55; 
  @ */
int Nmax (int p) {
  fp pp = 1, p2 = 1; int N;
  for (N = 0; ((p-1)*(pp+p2))/2 < 2 / 2^(-53); N++)
    {pp *= p; p2 *= p-2;};
  return N;
}

/*@ ensures \result==l_pmax(N); */
int pmax (int N) {
  int p;
  for (p = 1; N <= Nmax(p); p++);
  return p-1;
}



/*@ requires 2 <= p && (p-1)*(p-1)*N <= max_int &&
  @   \base_addr(B) != \base_addr(A) &&
  @   is_exact_int_mat_bounded_by(A,LDA,N,N,0,p-1)  &&
  @      is_exact_int_mat_bounded_by(B,LDB,N,K,0,p-1); 
  @ assigns B[0..(N-1)*LDB+K-1];
  @ ensures is_exact_int_mat_bounded_by(B,LDB,N,K,0,p-1); 
  @*/
void LZ_TRSM (int N, int K, int p,
	      fp *A, int LDA, fp *B, int LDB) {
  if (N <= Nmax(p)) {
    /*@ assert N <= 55; @*/
    DTRSM (N, K, A, LDA, B, LDB); DREMM (N, K, p, B, LDB);
  } else {
    int P = N/2, G = N - P;
    LZ_TRSM (G, K, p, A+P*(LDA+1), LDA, B+P*LDB, LDB);
    DGEMM_NEG (P, G, K, p, A+P, LDA, B+P*LDB, LDB, B, LDB);
    DREMM (P, K, p, B, LDB);
    LZ_TRSM (P, K, p, A, LDA, B, LDB);
  }
}

/*
Local Variables:
compile-command: "make bts0112"
End:
*/
