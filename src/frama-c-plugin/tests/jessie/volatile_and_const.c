


// Set up a reference to a read-only hardware register that is
// mapped in a hard-coded memory location.
const volatile int *hardwareRegister  = (const volatile int*)0x8000;
 
int main () {

  int currentValue, newValue;

  currentValue = *hardwareRegister; // Read the memory location
  newValue = *hardwareRegister; // Read it again
 
  // this should not be provable
  //@ assert currentValue == newValue;

  // this should generated an unprovable VC: Cannot write to a const location
  *hardwareRegister = 5; 

  return 0;
}

