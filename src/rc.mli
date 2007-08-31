

type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string
  | RCident of string

val from_file : string -> (string * (string * rc_value) list) list
