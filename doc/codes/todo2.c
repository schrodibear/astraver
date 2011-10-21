#pragma FloatModel(strict)
#pragma FloatModel(full)
#pragma JessieFloatRoundingMode(downward)
#pragma JessieFloatRoundingMode(...)

Rémonter tous les prédicats au langage ACSL : 

  // 5 modes d'arrondi
Nearest_even,To_zero,Round_up,Round_down,Nearest_away

  // Casting 
logic float float_of_real(rounding_mode m,real x);
logic double double_of_real(rounding_mode m,real x);

