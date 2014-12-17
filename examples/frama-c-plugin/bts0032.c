/* Frama-C BTS 0032

Status: open

yields:


bts0032.c:15:[jessie] failure: Unexpected exception.
                  Please submit bug report (Ref. "Extlib.NotYetImplemented("Interp.terms Tcomprehension")").

*/




int a[12][45] = {0, };

//@ assigns a[..][..];
void f(void)
{
  a[1][3] = 42;
}

void main(void)
{
  f();
}


/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0032.c"
End:
*/
