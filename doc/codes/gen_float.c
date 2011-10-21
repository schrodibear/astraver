  // 2 autres types    

type sign = Positive | Negative

type class = Finite | Infinite | Nan

  // 2 autres fonctions d'observation 

logic float_sign : gen_float -> sign 
logic float_class : gen_float -> class
