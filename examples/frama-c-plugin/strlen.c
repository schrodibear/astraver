#include <string.h>

// do not care about termination
#pragma JessieTerminationPolicy(user)

/*@ axiomatic String {
  @ logic integer strlen(char *s) reads s[0..];
  @ axiom strlen_pos_or_null:
  @   ∀ char* s; ∀ integer i;
  @       (0 ≤ i ≤ 2147483647
  @       ∧ (∀ integer j; 0 ≤ j < i ==> s[j] != '\0')
  @       ∧ s[i] == '\0') ==> strlen(s) == i;
  @
  @ axiom strlen_neg:
  @   ∀ char* s;
  @       (∀ integer i; 0 ≤ i ≤ 2147483647 ==> s[i] != '\0')
  @       ==> strlen(s) < 0;
  @ }
  @
  @ lemma strlen_upper_bound:
  @   ∀ char* s; strlen(s) ≤ 2147483647;
  @  
  @ lemma strlen_before_null:
  @   ∀ char* s; ∀ integer i; 0 ≤ i < strlen(s) ==> s[i] != '\0';
  @
  @ lemma strlen_at_null:
  @   ∀ char* s; 0 ≤ strlen(s) ==> s[strlen(s)] == '\0';
  @
  @  lemma strlen_not_zero:
  @    ∀ char* s; ∀ integer i;
  @        0 ≤ i ≤ strlen(s) ∧ s[i] != '\0' ==> i < strlen(s);
  @
  @ lemma strlen_zero:
  @   ∀ char* s; ∀ integer i;
  @       0 ≤ i ≤ strlen(s) ∧ s[i] == '\0' ==> i == strlen(s);
  @
  @ lemma strlen_sup:
  @   ∀ char* s; ∀ integer i;
  @       0 ≤ i ≤ 2147483647 ∧ s[i] == '\0' ==> 0 ≤ strlen(s) ≤ i;
  @
  @ lemma strlen_shift:
  @   ∀ char* s; ∀ integer i;
  @       0 ≤ i ≤ strlen(s) ==> strlen(s + i) == strlen(s) − i;
  @
  @ lemma strlen_create:
  @   ∀ char* s; ∀ integer i;
  @       0 ≤ i ≤ 2147483647 ∧ s[i] == '\0' ==> 0 ≤ strlen(s) ≤ i;
  @
  @ lemma strlen_create_shift:
  @   ∀ char* s; ∀ integer i; ∀ integer k;
  @       0 ≤ k ≤ i ≤ 2147483647 ∧ s[i] == '\0'
  @       ==> 0 ≤ strlen(s+k) ≤ i − k;
  @
  @ predicate valid_string(char *s) =
  @   0 ≤ strlen(s) ∧ \valid(s+(0..strlen(s)));
  @*/

/*@ requires valid_string(str);
  @ ensures \result == strlen(str);
  @*/
size_t cstrlen(const char *str) {
  const char *s;
  //@ ghost int i = 0;

  /*@ loop invariant 0 <= i <= strlen(str);
    @ loop invariant s == str + i;
    @*/
  for (s = str; *s; s+=1) /*@ ghost i++;*/  ;
  return (s - str);
}
