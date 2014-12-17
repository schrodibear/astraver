#pragma JessieFloatModel(full)

int main(){
  double a = 0. / 0.;

  //@ assert \is_NaN(a);
  double b = a;
  //@ assert \is_NaN(b);
  //@ assert a == b;
  //@ assert \eq_float(a,b);
}
