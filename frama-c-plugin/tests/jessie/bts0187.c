/* Frama-C BTS 0258

yields:


Error: Casting from type struct unsigned_char_P * to type int not allowed

Fixed in Why 2.20

*/



unsigned char * PTT;

#define BUTTON_SEL ((int)PTT & 0x10)

int main() {
    if(BUTTON_SEL) ;
    return 0;
}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0187.c"
End:
*/
