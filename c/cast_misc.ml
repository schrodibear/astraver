
open Ctypes
open Cast

let noattr n = { ctype_node = n; ctype_storage = No_storage;
		 ctype_const = false; ctype_volatile = false } 
