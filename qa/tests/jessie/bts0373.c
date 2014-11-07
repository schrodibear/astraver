/* Frama-C BTS 0373


Status: open

*/

/*@ global invariant toto: 0 == 1; */
/*@ ensures \result == 0; */
int main() { return 1; }


/*
Local Variables:
compile-command: "make bts0373"
End:
*/
