


module HeapVarSet = Set.Make(String)

type var_info =
    {
      var_name : string;
      mutable var_is_assigned : bool;
      mutable var_is_static : bool;
      mutable function_reads : HeapVarSet.t;
      mutable function_writes : HeapVarSet.t;
    }

let default_var_info x =
  { var_name = x; 
    var_is_assigned = false;
    var_is_static = false;
    function_reads = HeapVarSet.empty;
    function_writes = HeapVarSet.empty; 
  }

type logic_info =
    {
      logic_name : string;
      mutable logic_args : HeapVarSet.t;
    }

let default_logic_info x =
  { logic_name = x;
    logic_args = HeapVarSet.empty }

