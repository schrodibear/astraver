
 #define BETA_SAT     2.0

//@ ensures \result == \abs(x);
double fabs2(double x){
  if (x==0.0)   return 0.0;
  if (x>0.0)    return x;
  return -x;
}

/*@ requires \valid(AB) && \valid(CD);
    requires 1.0 <= *AB <= 4.0;
    requires 1.0 <= *CD <= 8.0;
    ensures *AB >= -BETA_SAT && *AB <= BETA_SAT
         && *CD >= -BETA_SAT && *CD <= BETA_SAT;
 */
void Limit (float * AB, float * CD)
 {
  double max,Fabs_AB, Fabs_CD;

    Fabs_AB = fabs2 (*AB);
    Fabs_CD = fabs2 (*CD);

    max = Fabs_AB;
    if (Fabs_CD > Fabs_AB)
       max = Fabs_CD;

    if (max > BETA_SAT)
    {
       *AB = (float) (((*AB) * BETA_SAT) / max);
       *CD = (float) (((*CD) * BETA_SAT) / max);
    }

 }

