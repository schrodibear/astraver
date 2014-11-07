/*@ axiomatic StrLen {
    logic ℤ strlen{L}(char *s);
    // reads s[0..];
   
    axiom strlen_pos_or_null{L}:
      \forall char* s; \forall ℤ i;
         (0 <= i
          && (\forall ℤ j; 0 <= j < i ==> s[j] != '\0')
          && s[i] == '\0') ==> strlen(s) == i;
   
    axiom strlen_neg{L}:
      \forall char* s;
         (\forall ℤ i; 0 <= i ==> s[i] != '\0')
         ==> strlen(s) < 0;
   
    axiom strlen_before_null{L}:
      \forall char* s; \forall ℤ i; 0 <= i < strlen(s) ==> s[i] != '\0';
   
    axiom strlen_at_null{L}:
      \forall char* s; 0 <= strlen(s) ==> s[strlen(s)] == '\0';
   
    axiom strlen_not_zero{L}:
      \forall char* s; \forall ℤ i;
         0 <= i <= strlen(s) && s[i] != '\0' ==> i < strlen(s);
   
    axiom strlen_zero{L}:
      \forall char* s; \forall ℤ i;
         0 <= i <= strlen(s) && s[i] == '\0' ==> i == strlen(s);
   
    axiom strlen_sup{L}:
      \forall char* s; \forall ℤ i;
         0 <= i && s[i] == '\0' ==> 0 <= strlen(s) <= i;
   
    axiom strlen_shift{L}:
      \forall char* s; \forall ℤ i;
         0 <= i <= strlen(s) ==> strlen(s + i) == strlen(s) - i;
   
    axiom strlen_create{L}:
      \forall char* s; \forall ℤ i;
         0 <= i && s[i] == '\0' ==> 0 <= strlen(s) <= i;
   
    axiom strlen_create_shift{L}:
      \forall char* s; \forall ℤ i; \forall ℤ k;
         0 <= k <= i && s[i] == '\0' ==> 0 <= strlen(s+k) <= i - k;
    }
  */

/*@ predicate valid_string{L}(char *s) =
      0 <= strlen(s) && \valid(s+(0..strlen(s)));
   
    predicate valid_string_or_null{L}(char *s) =
      s == \null || valid_string(s);
  */

