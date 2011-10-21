  // Comparaisons et opérations élémentaires

  // Prédicats
predicate is_nan_float(float x);
predicate is_nan_double(double x);
predicate is_finite_float(float x);
predicate is_finite_double(double x);
predicate is_infinite_float(float x);
predicate is_infinite_double(double x);

  // Erreurs d'arrondi
round_error(e) et total_error(e)
