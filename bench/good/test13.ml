
external x,y: int ref

external visible : 
  (a:int)(b:int)
  returns result:bool pre  pre_visible(a,b)
                      post post_visible(a,b,result) end

let p = if !x = 0 && (visible !x !y) then x := !y

