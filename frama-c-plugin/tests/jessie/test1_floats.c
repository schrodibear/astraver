
#pragma JessieFloatModel(strict)

/*@ requires \abs(x) <= 0x1p-5; 
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;  
  @*/
float moncos(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;
  return 1.0f - x * x * 0.5f;
}


