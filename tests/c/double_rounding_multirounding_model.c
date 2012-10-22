
/* 

Warning: the proof can be achieve with Gappa 0.14.1 but not
with versions 0.15 ou 0.16. Hopefully it will work with 0.16.1 and higher

*/

#pragma JessieFloatModel(multirounding)

double doublerounding() {
  double x = 1.0;
  double y = 0x1p-53 + 0x1p-64;
  double z = x + y;
  //@ assert 1.0 - 0x1p-63 <= z <= 1.0 + 0x1p-52 + 0x1p-62;
  // assert 1.0 <= z <= 1.0 + 0x1p-52;
  return z;
}

/*
Local Variables:
compile-command: "LC_ALL=C make double_rounding_multirounding_model.why3ide"
End:
*/
