/**************************************************************************/
/*                                                                        */
/*  The Why/Caduceus/Krakatoa tool suite for program certification        */
/*  Copyright (C) 2002-2006                                               */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
/*    Yannick MOY                                                         */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU General Public                   */
/*  License version 2, as published by the Free Software Foundation.      */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/*  See the GNU General Public License version 2 for more details         */
/*  (enclosed in the file GPL).                                           */
/*                                                                        */
/**************************************************************************/

typedef struct {
	int Pn;
	int CPRE_Pn;
	int Nivpn;
	int CPRE_Nivpn;
	int CPRE_VC[4];
	int VC[4];
	int * Cpt[4];
	int Param;
	int Param4_Pn;
	int V;
	} MaStruct;
int Ch_Pn[4];
int SPMEP[4];

/*@ requires \valid(Parametre) && \valid_range(Pn_Bac, 0, 4);
  @*/
void V4A (MaStruct *Parametre,int Val_Boitier [ 4 ],int Pn_Bac [ 4 ],MaStruct *Parametre_Ref)
{
  Parametre->VC[0] = ! ( Ch_Pn[0] || Pn_Bac[0] || SPMEP[0] );
  Parametre->VC[1] = ! ( Ch_Pn[1] || Pn_Bac[1] || SPMEP[1] );
  Parametre->VC[2] = ! ( Ch_Pn[2] || Pn_Bac[2] || SPMEP[2] );
  Parametre->VC[3] = ! ( Parametre->Param4_Pn || Pn_Bac[3]);
}

/*
Local Variables:
compile-command: "make ifs"
End:
*/