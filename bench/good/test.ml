
let test_let = 
  (let x = ref 0 in
   if !x > 0 then x := !x - 1 else x := !x + 1)
  { x = 1 }

