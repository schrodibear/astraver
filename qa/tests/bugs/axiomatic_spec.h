
#define PDPL_EHOLE 0x1
#define PDPL_CCNR  0x2
#define PDPL_CCNRI 0x4

// ghost enum LabelSecFlag {EHOLE = PDPL_EHOLE, CCNR = PDPL_CCNR, CCNRI = PDPL_CCNRI};
//@ ghost enum IntLevel     {LowInt, HighInt};
/*@ axiomatic ParsecTypes {
       type Label;
       type LabelCnfLevel      = integer;
       type LabelIntLevel      = enum IntLevel ;//{ EHOLE , CCNR , CCNRI };

       type LabelCnfCategory   = integer;

       logic boolean isGtVarType(LabelIntLevel l1, LabelIntLevel l2) = l1 > l2;
       
//        axiom category_positive:
//             \forall LabelCnfCategory c; c >= 0;

       type LabelCnfCategories = set<LabelCnfCategory>;
       type LabelSecFlag       = enum LabelSecFlag;
       type LabelSecFlags      = set<LabelSecFlag>;


//        logic Label newLabel(LabelCnfLevel l, LabelIntLevel il, LabelCnfCategories c, LabelSecFlags f);
//        logic LabelCnfLevel      getCnfLevel(Label l);
//        logic LabelIntLevel      getIntLevel(Label l);
//        logic LabelCnfCategories getCnfCategories(Label l);
//        logic LabelSecFlags      getSecFlags(Label l);

//        axiom LabelFieldAccess:
//           \forall LabelCnfLevel l, LabelIntLevel il, LabelCnfCategories c, LabelSecFlags f;
//                 l  == getCnfLevel(newLabel(l, il, c, f))      &&
//                 il == getIntLevel(newLabel(l, il, c, f))      &&
//                 c  == getCnfCategories(newLabel(l, il, c, f)) &&
//                 f  == getSecFlags(newLabel(l, il, c, f));
    }
 */

//             let nl = newLabel(l, il, c, f);
