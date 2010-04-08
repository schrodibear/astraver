/*@ axiomatic a1 {
    logic boolean isList{L}(int *b, integer f) reads b[5];
    logic integer jLgth{L}(int *b) reads \nothing;
    axiom a2{L}: \forall int *b; isList(b,b[5]);
    axiom a3{L}: \forall int *b; jLgth(b) == 0;
} */ 
