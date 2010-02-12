/* Frama-C BTS 0404


Status: open

*/

// typedef struct abstract_seq_call {int bidon;} SEQ_CALL;
typedef struct abstract_seq_call {int bidon;} SEQ_CALL;

/*@ axiomatic Seq_call {
  @     logic SEQ_CALL nocall ;
  @     logic SEQ_CALL callto(integer call_id) ;
  @     logic SEQ_CALL addcallto(SEQ_CALL seq, integer call_id) ;
  @
  @     axiom A: 
  @       \forall integer id ;
  @       callto(id)==addcallto(nocall,id);
  @ }
  @*/

int main(void) {return 0;}



/*
Local Variables:
compile-command: "make bts0404"
End:
*/
