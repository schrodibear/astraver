
(*s types and environments *)

type accessibility = Apublic | Aprotected | Aprivate | Anone

type base_type =
    | Tshort | Tboolean | Tbyte | Tchar | Tint | Tfloat | Tlong | Tdouble 
	  (* native logic types *)
    | Tinteger | Treal | Tunit

type java_type =
    | JTYbase of base_type
    | JTYnull (*r type of 'null' *)
    | JTYclass of bool * java_class_info (*r first arg true if non_null *)
    | JTYinterface of interface_info 
    | JTYarray of java_type

   
and java_var_info =
    {
      java_var_info_tag : int;
      java_var_info_name : string;
      mutable java_var_info_final_name : string;
      mutable java_var_info_assigned : bool;
      java_var_info_type : java_type;
    }
    
and java_field_info =
    {
      java_field_info_tag : int;
      java_field_info_name : string;
      java_field_info_class : java_class_info;
(*
      mutable java_field_info_trans_name : string;
      java_field_info_accessibility : accessibility;
*)
      java_field_info_is_static : bool;
      java_field_info_is_final : bool;
(*
      java_field_info_class_or_interface : java_env_entry;
*)
      java_field_info_type : java_type;
(*
      java_field_info_is_ghost : bool;
      java_field_info_is_model : bool;
*)
    }
    
(*
and constant_entry =
    {
      constant_entry_name : string;
      constant_entry_interface : interface_entry;
      constant_entry_type : java_type;
    }
*)

and method_info = 
    {
     method_info_tag : int;
     method_info_name : string;
     mutable method_info_trans_name : string;
     method_info_is_static : bool;
(*
     method_info_accessibility : accessibility;
*)
(*
     method_info_class_or_interface : java_env_entry;
     mutable method_info_is_predicate : bool;
     method_info_routine :  routine_entry;
     method_info_sep_specs : string list;
     mutable method_info_graph : java_env_entry list
*)
     mutable method_info_has_this : java_var_info option;
     method_info_parameters : java_var_info list;
     method_info_result : java_var_info option ;
     mutable method_info_calls : method_info list;
   }

and constructor_info = 
    {
      constr_info_tag : int;
      constr_info_class : java_class_info;
      mutable constr_info_trans_name : string;
      mutable constr_info_this : java_var_info option;
      mutable constr_info_result : java_var_info option;
      constr_info_parameters : java_var_info list;
      constr_info_calls : method_info list;
(*
     mutable constructor_entry_graph : java_env_entry list
*)
    }

    
and logic_type_entry =
    {
      mutable logic_type_entry_name : string
    }

and java_logic_info =
    {
      java_logic_info_name : string;
      java_logic_info_tag : int;
      java_logic_info_result_type : java_type option;
      java_logic_info_parameters : java_var_info list;
      mutable java_logic_info_calls : java_logic_info list;
    }


and axiom_info = 
    {
      axiom_info_name : string;
(*
      mutable axiom_info_effects : effects ;
*)
    }
    

(*
and effects = 
    {
      reads_alloc : bool;
      writes_alloc : bool;
      writes_everything : bool;
      reads_alloc_table : bool;
      writes_alloc_table : bool;
(*
      reads : java_field_info Inttagset.t;
      writes : java_field_info Inttagset.t;
*)
      reads_int_array : bool;
      reads_int_assigned_array : bool;
      writes_int_array : bool;
      reads_float_array : bool;
      writes_float_array : bool;
      reads_bool_array : bool;
      writes_bool_array : bool;
      reads_obj_array : bool;
      writes_obj_array : bool;
      throws : bool (*i class_entry Inttagset.t i*);
      breaks : bool (*i label_entry Inttagset.t i*);
      continue : bool
    }
*)

and package_info =
    {
      package_info_tag : int;
      package_info_name : string;
      package_info_directory : string;
    }
    
and java_class_info =
    {
      class_info_tag : int;
      class_info_name : string;
(*
      mutable class_info_fields : java_field_info list;
      mutable class_info_methods : method_info list;
      mutable class_info_constructors : constructor_info list;
*)
      mutable class_info_extends : java_class_info option;
      mutable class_info_is_exception : bool;
      mutable class_info_implements : interface_info list;
    }

and interface_info =
    {
      interface_info_tag : int;
      interface_info_name : string;
      mutable interface_info_extends : interface_info list;
(*
      mutable interface_info_fields : java_field_info list;
      mutable interface_info_methods : method_info list;
*)
    }

and java_type_info =
  | TypeClass of java_class_info
  | TypeInterface of interface_info

(*s literals, shared between ASTs and typed ASTs *)

type literal =
    | Integer of string
    | Float of string
    | Bool of bool
    | String of string
    | Char of string
    | Null


(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
