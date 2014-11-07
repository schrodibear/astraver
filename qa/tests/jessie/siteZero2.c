#define BOUND 0x1p-20

#define T 0.015625
#define KG1  0.99838542645959
#define KG2 10.3020010835769
#define MIT 3.986005E+005

/*@ requires x > 0.0;
    assigns \nothing;
    ensures \abs(\result - \sqrt(x)) <= BOUND;
    ensures \result > 0.0;
*/
double sqrt(double x);

struct
     {
       float x1, y1, z1, xx,xz,y,yy,r1;
     } M;

struct
{
    float Fixy,Fixz, Fiyz,M1x, M1y, M1z, M1r,Mxx, Myy,Mxz,My;
} L;

typedef struct
{
  double x, y, z;
} COMPVETOR;

COMPVETOR  D;

extern struct
{
      float Mx,My,Mz;
} Escala;

struct
{
  short int Fx,Fy,Fz;
} Vel_Lin;

extern struct
{
  double P0_X,P0_Y,P0_Z;
} Cmd;


float Wae;
float Nav_G;
float Grav;

/*@ requires \abs(Cmd.P0_X - 6.378291E+3) <= BOUND && \abs(Cmd.P0_Y - (-1.659630E+0)) <= BOUND && \abs(Cmd.P0_Z - 0.4758900)<= BOUND;
    requires \abs(Escala.Mx - 0.03) <= BOUND && \abs(Escala.My - 0.03) <= BOUND && \abs(Escala.Mz - 0.03) <= BOUND;
    requires 5 <=  Vel_Lin.Fx <=29;
    requires -1 <= Vel_Lin.Fy <=1;
    requires 0 <=  Vel_Lin.Fz <=12;

    requires \abs(L.M1x)<=BOUND && \abs(L.M1y)<= BOUND && \abs(L.M1z)<= BOUND &&
           \abs(L.Mxx)<= BOUND && \abs(L.Mxz)<= BOUND && \abs(L.Myy)<= BOUND &&
           \abs(L.My )<= BOUND && \abs(L.M1r)<= BOUND && \abs(L.Fixy)<= BOUND && \abs(L.Fixz)<= BOUND && \abs(L.Fiyz)<= BOUND;

    requires \abs(Wae) <= BOUND;

*/

void Test(void)
 {
   float result;
   float Modulo;
   double Adcc_Vx,Adcc_Vy,Adcc_Vz;
   double aux,R;


   Grav = (float) MIT;
   //@ assert \abs( Grav - MIT) <= BOUND;

   aux =   (Cmd.P0_X * Cmd.P0_X +  Cmd.P0_Y * Cmd.P0_Y + Cmd.P0_Z * Cmd.P0_Z);

   //@ assert aux > 0.0;
    Modulo = sqrt(aux);
   //@ assert Modulo > 0.0;

   //@ assert Modulo - KG2 !=0.0;
     Nav_G =  (float)KG1 * Grav / ( (Modulo - (float)KG2) * (Modulo - (float)KG2) ) ;
    //@ assert Nav_G > 0.0;

    Adcc_Vx = ((Escala.Mx * (float)Vel_Lin.Fx ) -  (L.Fixy * Escala.My * (float)Vel_Lin.Fy) - (L.Fixz * Escala.Mz * (float)Vel_Lin.Fz) ) / 1000.0;
   //@ assert Adcc_Vx >= 0.0;

    Adcc_Vy =((Escala.My * (float)Vel_Lin.Fy ) - (L.Fiyz *Escala.Mz * (float)Vel_Lin.Fz) ) / 1000.0;

    Adcc_Vz = (Escala.Mz * (float)Vel_Lin.Fz)/1000.0;
   //@ assert Adcc_Vz >= 0.0;


 //@ assert \abs(L.M1x)<=BOUND && \abs(L.M1y)<= BOUND && \abs(L.M1z)<= BOUND && \abs(L.Mxx)<= BOUND && \abs(L.Mxz)<= BOUND && \abs(L.Myy)<= BOUND && \abs(L.My)<= BOUND && \abs(L.M1r)<= BOUND;

  M.x1 = L.M1x / 3600.0;
  //@ ghost float tmp1 = L.M1x / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.x1;
  //@ assert \abs(M.x1) <= BOUND;

    M.y1 = L.M1y / 3600.0;
  //@ ghost tmp1 = L.M1y / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.y1;
  //@ assert \abs(M.y1) <= BOUND;

  M.z1 = L.M1z / 3600.0;
  //@ ghost tmp1 = L.M1z / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.z1;
  //@ assert \abs(M.z1) <= BOUND;

  M.xx = L.Mxx / 3600.0;
  //@ ghost tmp1 = L.Mxx / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.xx;
  //@ assert \abs(M.xx) <= BOUND;

  M.xz = L.Mxz / 3600.0;
  //@ ghost tmp1 = L.Mxz / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.xz;
  //@ assert \abs(M.xz) <= BOUND;

  M.yy = L.Myy / 3600.0;
  //@ ghost tmp1 = L.Myy / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.yy;
  //@ assert \abs(M.yy) <= BOUND;

  M.y  = L.My  / 3600.0;
  //@ ghost tmp1 = L.My / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.y;
  //@ assert \abs(M.y)  <= BOUND;

  M.r1 = L.M1r / 3600.0;
  //@ ghost tmp1 = L.M1r / 3600.0;
  //@ assert \abs(tmp1) <= BOUND;
  //@ assert tmp1 == M.r1;
  //@ assert \abs(M.r1) <= BOUND;

  D.x = (M.x1 * T) + (M.xx *Adcc_Vx / Nav_G) +  (M.xz * Adcc_Vz / Nav_G)  - (Wae * Adcc_Vx * Adcc_Vy / (T * Nav_G * Nav_G));

  //@ ghost double tmp2 = (M.x1 * T) + (M.xx * Adcc_Vx / Nav_G) + (M.xz * Adcc_Vz / Nav_G) - (Wae * Adcc_Vx * Adcc_Vy /(T * Nav_G * Nav_G));
  //@ assert \abs(tmp2) <= BOUND;
  //@ assert D.x == \round_float(\Single,\NearestEven,tmp2);
  //@ assert \abs(D.x) <= BOUND;

  D.y=Nav_G;

  //@ assert \abs(D.x) > 0.0 || \abs(D.x) > 0.0;
  aux =   (D.x * D.x) + (D.y * D.y);

  //@ assert aux > 0.0;
    R = sqrt(aux);
  //@ assert R > 0.0;
  //@ assert R - KG2 !=0.0;

  result =  (float)KG1 * Grav / ( (R - (float)KG2) * (R - (float)KG2) ) ;



}
