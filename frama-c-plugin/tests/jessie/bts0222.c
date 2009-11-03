/* Frama-C BTS 0080

Status: closed

Was already fixed before, although not mentioned in CHANGES

probably fixed by F Bobot

*/

/*@ logic integer max_index { L }( int t [] , integer n ) =
  @ ( n ==0) ? 0 :
  @ ( t [n -1]==0) ? n : max_index (t , n -1);
  @*/



/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0222.c"
End:
*/



