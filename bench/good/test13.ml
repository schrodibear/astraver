
external x,y: int ref

external visible : 
  a:int -> b:int ->
  { pre_visible(a,b) } returns result:bool { post_visible(a,b,result) }

let p = if !x = 0 && (visible !x !y) then x := !y

