
(*s literals *)

type literal =
    | Integer of string
    | Float of string
    | Bool of bool
    | String of string
    | Char of string
    | Null

(*s types and environments *)

type accessibility = [ `PUBLIC | `PROTECTED | `PRIVATE | `NONE ];;

type base_type =
    | Tshort | Tboolean | Tbyte | Tchar | Tint | Tfloat | Tlong | Tdouble 
	  (* native logic types *)
    | Tinteger | Treal | Tnull

type java_type =
    | JTYbase of base_type
    | JTYclass of bool * java_class_info (*r first arg true if non_null *)
    | JTYarray of java_type

(*
type java_type =
  | Byte_type
  | Short_type
  | Integer_type
  | Float_type
  | Boolean_type
  | Null_type
  | Type_type
  | Class_type of class_entry
  | Interface_type of interface_entry
  | Array_type of java_type
  | Prop_type
  | Logic_type of string
*)
    
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
      java_field_info_is_static : bool;
      java_field_info_is_final : bool;
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
     method_info_return_type : java_type option ;
   }
    
and logic_type_entry =
    {
      mutable logic_type_entry_name : string
    }

(*
and logic_entry = 
    {
      logic_entry_name : string;
      logic_entry_return_type : java_type;
      mutable logic_entry_effects : effects ;
      logic_entry_parameters : t;
    }
*)
    
and java_logic_info =
    {
      java_logic_info_name : string;
      java_logic_info_tag : int;
      java_logic_info_result_type : java_type option;
      java_logic_info_parameters : java_var_info list;
(*
      java_logic_info_effects = empty_effects;
*)
      java_logic_info_calls : java_logic_info list;
    }


and axiom_entry = 
    {
      axiom_entry_name : string;
      mutable axiom_entry_effects : effects ;
    }
    
and constructor_entry = 
    {
     mutable constructor_entry_trans_name : string;      
     constructor_entry_class : java_class_info;
     constructor_entry_routine : routine_entry;
     mutable constructor_entry_graph : java_env_entry list
    }

and routine_entry =
    {
     routine_entry_parameters : t;
(*
     mutable routine_entry_parameters_as_local_var : t;
     mutable routine_entry_produce_body : bool;
     mutable routine_entry_local_vars : t;
     mutable routine_entry_effects : effects;
     mutable routine_entry_int_array_writes_nothing : bool;
     mutable routine_entry_float_array_writes_nothing : bool;
     mutable routine_entry_bool_array_writes_nothing : bool;
     mutable routine_entry_obj_array_writes_nothing : bool;
     mutable routine_entry_fields_writes_nothing : 
       java_field_info Inttagset.t;
     mutable routine_entry_use_transactions : bool
       *)
   }

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

and package_entry =
    {
      package_entry_name : string;
      mutable package_entry_directories : string list;
      mutable package_entry_contents_read : bool;
      mutable package_entry_contents : t;
    }
    
and java_class_info =
    {
(*
      class_entry_package : string;
*)
      class_info_name : string;
      mutable class_info_fields : java_field_info list;
(*
      mutable class_entry_extends : class_entry option;
      mutable class_entry_implements : interface_entry list;
      mutable class_entry_contents : t;
      mutable class_entry_constructors : constructor_entry list;
      mutable class_entry_invariant_effects : effects;
      mutable class_entry_static_invariant_effects : effects;
*)
(*
      mutable class_entry_invariant_args : (string * Why.base_type) list;
      mutable class_entry_static_invariant_args : (string * Why.base_type) list;
      mutable class_entry_restore_invariant_args : (string * Why.base_type) list;
      mutable class_entry_representation_invariant_effects : effects;
*)
    }

and interface_entry =
    {
      interface_entry_name : string;
      mutable interface_entry_extends : interface_entry list;
      mutable interface_entry_contents : t;
    }

and java_env_entry = 
(*
  | Package_entry of package_entry
  | Class_entry of class_entry
  | Interface_entry of interface_entry
*)
  | Instance_variable_entry of java_field_info
(*
  | Constant_entry of constant_entry
  | Method_entry of method_info list
  | Constructor_entry of constructor_entry
*)
  | Local_variable_entry of java_var_info 
(*
  | Logic_type_entry of logic_type_entry 
  | Logic_entry of java_logic_info
*)

and t = (string * java_env_entry) list
;;

(*
Local Variables: 
compile-command: "make -C .. bin/krakatoa.byte"
End: 
*)
