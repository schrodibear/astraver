

double doublerounding() {
  double x = 1.0;
  double y = 0x1p-53 + 0x1p-64;
  double z = x + y;
  //@ assert z == 1.0 + 0x1p-52;
  return z;
}


/*
Local Variables:
compile-command: "LC_ALL=C make double_rounding_strict_model.why3ide"
End:
*/
