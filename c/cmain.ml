
let c_parser c = 
  let d = Clexer.parse c in
  let p = Cinterp.interp d in
  p

