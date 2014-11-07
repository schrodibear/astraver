
#include "kernel.h"
#include "module.h"

#define PDPL_EHOLE 0x1
#define PDPL_CCNR  0x2
#define PDPL_CCNRI 0x4

/*@ type CnfCategory = integer;
  @
  @ axiomatic CnfCategorySetTheory {
  @ type CnfCategorySet;
  @
  @ logic CnfCategorySet EmptyCnfCategorySet;
  @ logic CnfCategorySet addCnfCategory(CnfCategorySet s, CnfCategory c);
  @ logic CnfCategorySet intersectCnfCategorySet(CnfCategorySet s1, CnfCategorySet s2);
  @ logic boolean isinCnfCategorySet(CnfCategorySet s, CnfCategory c);
  @ logic integer sizeCnfCategorySet(CnfCategorySet s);
  @
  @ axiom add2Set:
  @  \forall CnfCategorySet s, CnfCategory c; addCnfCategory(addCnfCategory(s,c),c) == addCnfCategory(s,c);
  @
  @ axiom addCnfCategory_trans:
  @  \forall CnfCategorySet s, CnfCategory i, CnfCategory j; addCnfCategory(addCnfCategory(s,i),j) == addCnfCategory(addCnfCategory(s,j),i);
  @
  @ axiom isinEmptySet:
  @  \forall CnfCategory c; isinCnfCategorySet(EmptyCnfCategorySet,c) == \false;
  @
  @ axiom isinAddCnfCategory1:
  @  \forall CnfCategorySet s, CnfCategory c; isinCnfCategorySet(addCnfCategory(s,c),c);
  @
  @ axiom isinAddCnfCategory2:
  @  \forall CnfCategorySet s, CnfCategory i, CnfCategory j; (i != j) ==> (isinCnfCategorySet(addCnfCategory(s,i),j) == isinCnfCategorySet(s,j));
  @
  @ axiom intersect_com:
  @  \forall CnfCategorySet s1, CnfCategorySet s2; intersectCnfCategorySet(s1,s2) == intersectCnfCategorySet(s2,s1);
  @
  @ axiom intersect_trans:
  @  \forall CnfCategorySet s1, CnfCategorySet s2, CnfCategorySet s3;
  @    intersectCnfCategorySet(s1,intersectCnfCategorySet(s2,s3)) == intersectCnfCategorySet(intersectCnfCategorySet(s1,s2),s3);
  @
  @ axiom intersect_def0:
  @  \forall CnfCategorySet s; intersectCnfCategorySet(EmptyCnfCategorySet,s) == EmptyCnfCategorySet;
  @
  @ axiom intersect_def1:
  @  \forall CnfCategorySet s1, CnfCategorySet s2, CnfCategory c;
  @    isinCnfCategorySet(s1,c) && isinCnfCategorySet(s2,c) <==> isinCnfCategorySet(intersectCnfCategorySet(s1,s2),c);
  @
  @ axiom sizeCnfCategorySet_def0:
  @  sizeCnfCategorySet(EmptyCnfCategorySet) == 0;
  @
  @ axiom sizeCnfCategorySet_def1:
  @  \forall CnfCategorySet s, CnfCategory e;
  @    isinCnfCategorySet(s,e) ==> sizeCnfCategorySet(addCnfCategory(s,e)) == sizeCnfCategorySet(s);
  @
  @ axiom sizeCnfCategorySet_def2:
  @  \forall CnfCategorySet s, CnfCategory e;
  @    !isinCnfCategorySet(s,e) ==> sizeCnfCategorySet(addCnfCategory(s,e)) == sizeCnfCategorySet(s)+1;
  @
  @ lemma intset_intersect_prop:
  @     \forall CnfCategorySet s1,s2;
  @         sizeCnfCategorySet(intersectCnfCategorySet(s1,s2)) <= \min(sizeCnfCategorySet(s1),sizeCnfCategorySet(s2));
  @
  @ }
  @*/

//@ ghost enum IntLevel     {LowInt, HighInt};
/*@ axiomatic ParsecTypesTheory {
       type Label;
       type LabelCnfLevel       = integer;
       type LabelIntLevel       = enum IntLevel;
       type LabelCnfCategorySet = CnfCategorySet;
       type LabelSecFlag        = boolean;


       logic Label newLabel(LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri);
       logic LabelCnfLevel       getCnfLevel(Label l);
       logic LabelIntLevel       getIntLevel(Label l);
       logic LabelCnfCategorySet getCnfCategorySet(Label l);
       logic LabelSecFlag        getSecFlagEHOLE(Label l);
       logic LabelSecFlag        getSecFlagCCNR(Label l);
       logic LabelSecFlag        getSecFlagCCNRI(Label l);

       axiom LabelFieldAccessCnfLevel:
          \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri;
                l  == getCnfLevel(newLabel(l, il, c, ehole, ccnr, ccnri));

       axiom LabelFieldAccessIntLevel:
          \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri;
                il == getIntLevel(newLabel(l, il, c, ehole, ccnr, ccnri));

       axiom LabelFieldAccessCnfCategorySet:
          \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri;
                c  == getCnfCategorySet(newLabel(l, il, c, ehole, ccnr, ccnri));

       axiom LabelFieldAccessEHOLE:
          \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri;
                ehole == getSecFlagEHOLE(newLabel(l, il, c, ehole, ccnr, ccnri));

       axiom LabelFieldAccessCCNR:
          \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri;
                ccnr  == getSecFlagCCNR(newLabel(l, il, c, ehole, ccnr, ccnri));

       axiom LabelFieldAccessCCNRI:
          \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategorySet c, LabelSecFlag ehole, LabelSecFlag ccnr, LabelSecFlag ccnri;
                ccnri == getSecFlagCCNRI(newLabel(l, il, c, ehole, ccnr, ccnri));

    }
 */

/*@ axiomatic ParsecTypes {
    //logic LabelIntLevel i2m_IntLevel(PDP_ILEV_T il) = (il == 0) ? LowInt : HighInt;
    logic enum IntLevel i2m_IntLevel(PDP_ILEV_T il) = ((il == 0) ? LowInt : HighInt);

    logic LabelCnfCategorySet i2m_CnfCategorySet64(PDP_CAT_T c, integer n) =
       n == 0 ? EmptyCnfCategorySet :
          \let prev_set = i2m_CnfCategorySet64(((PDP_CAT_T) (c << 1)), n - 1);
          ((c | 0x1) == 1) ? addCnfCategory(prev_set, 64 - n) : EmptyCnfCategorySet;

    logic LabelCnfCategorySet i2m_CnfCategorySet(PDP_CAT_T c) = i2m_CnfCategorySet64(c, 64);

    logic LabelSecFlag i2m_SecFlagEHOLE(PDP_TYPE_T t) = t & PDPL_EHOLE ? \true : \false;
    logic LabelSecFlag i2m_SecFlagCCNR(PDP_TYPE_T t)  = t & PDPL_CCNR  ? \true : \false;
    logic LabelSecFlag i2m_SecFlagCCNRI(PDP_TYPE_T t) = t & PDPL_CCNRI ? \true : \false;

    logic Label i2m_Label{L}(PDP_LABEL_T *l) =
       newLabel(l->lev, i2m_IntLevel(l->ilev), i2m_CnfCategorySet(l->cat), i2m_SecFlagEHOLE(l->type), i2m_SecFlagCCNR(l->type), i2m_SecFlagCCNRI(l->type));
    }
 */

