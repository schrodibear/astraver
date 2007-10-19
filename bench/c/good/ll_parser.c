
/* LL parser */

/* grammar for arithmetic expressions:

     E ::= T | T "+" E 
     E ::= F | F "*" T
     F ::= "id" | "(" E ")"

*/

enum T { PLUS, MULT, LPAR, RPAR, ID, EOF };
typedef enum T token;

token *text; // should be ghost?

//@ ensures \result == *text
token next_token();

//@ ensures text == text+1
void advance();

/*@ requires 1 // TODO
  @ ensures  0 // never returns
  @*/
void parse_error();

/*@ requires 1 // TODO
  @ ensures  0 // never returns
  @*/
void success();

void parse_S();
void parse_E();
void parse_T();
void parse_F();

void parse_S() {
  parse_E();
  if (next_token() == EOF) 
    success(); 
  else 
    parse_error();
}

void parse_E() {
  parse_T();
  switch (next_token()) {
  case PLUS: 
    advance(); 
    parse_E(); 
    return;
  default: 
    return;
  }
}

void parse_T() {
  parse_F();
  switch (next_token()) {
  case MULT: 
    advance(); 
    parse_T(); 
    return;
  default: 
    return;
  }
}

void parse_F() {
  switch (next_token ()) { 
  case ID: 
    advance();
    return;
  case LPAR:
    advance();
    parse_E();
    switch (next_token()) { 
    case RPAR: 
      advance();
      return;
    default:
      parse_error();
    }
  default:
    parse_error();
  }
}

